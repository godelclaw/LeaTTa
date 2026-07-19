#!/usr/bin/env python3

import builtins
import enum
import importlib
import importlib.util
import json
import os
import struct
import sys
import time
from collections.abc import Iterator, Sequence


objects = {}
object_handles = {}
next_handle = 1
resources = {}
next_resource = 1


def load_call_fixture():
    """Load a strict synthetic call policy for offline live-record runs.

    Imports still execute their real module initializers.  Calls are either
    explicitly allowed as local/pure or answered from the ordered fixture;
    every other Python call fails closed before its target is invoked.
    """
    path = os.environ.get("PLEATTA_CALL_FIXTURE", "")
    if not path:
        return None
    with open(path, encoding="utf-8") as handle:
        fixture = json.load(handle)
    return {
        "allow": set(fixture.get("allow", [])),
        "responses": list(fixture.get("responses", [])),
        "cursor": 0,
    }


call_fixture = load_call_fixture()


def tagged(name, field=None, value=None):
    if field is None:
        return name
    return {name: {field: value}}


def decode_value(encoded):
    if encoded == "none":
        return None
    if not isinstance(encoded, dict) or len(encoded) != 1:
        raise TypeError("malformed HostValue")
    tag, payload = next(iter(encoded.items()))
    if tag == "integer":
        return int(payload["value"])
    if tag == "floating":
        bits = int(payload["bits"])
        return struct.unpack(">d", struct.pack(">Q", bits))[0]
    if tag == "string":
        return payload["value"]
    if tag == "boolean":
        return bool(payload["value"])
    if tag == "list":
        return [decode_value(item) for item in payload["items"]]
    if tag == "tuple":
        return tuple(decode_value(item) for item in payload["items"])
    if tag == "mapping":
        return {
            key: decode_value(value)
            for key, value in payload["items"]
        }
    if tag == "handle":
        handle = int(payload["id"])
        if handle not in objects:
            raise ReferenceError(f"unknown Python object handle {handle}")
        return objects[handle]
    if tag == "resource":
        raise TypeError("host resources cannot cross into a Python call")
    raise TypeError(f"unsupported HostValue constructor {tag}")


def float_bits(value):
    return str(struct.unpack(">Q", struct.pack(">d", value))[0])


def opaque_handle(value):
    global next_handle
    identity = id(value)
    previous = object_handles.get(identity)
    if previous is not None and objects.get(previous) is value:
        return previous
    handle = next_handle
    next_handle += 1
    objects[handle] = value
    object_handles[identity] = handle
    return handle


def encode_value(value):
    if value is None:
        return "none"
    if isinstance(value, bool):
        return tagged("boolean", "value", value)
    if isinstance(value, int):
        return tagged("integer", "value", value)
    if isinstance(value, float):
        return tagged("floating", "bits", float_bits(value))
    if isinstance(value, str):
        return tagged("string", "value", value)
    if isinstance(value, enum.Enum):
        return tagged("string", "value", value.name)
    if isinstance(value, list):
        return tagged("list", "items", [encode_value(item) for item in value])
    if isinstance(value, tuple):
        return tagged("tuple", "items", [encode_value(item) for item in value])
    if isinstance(value, dict):
        items = []
        for key in sorted(value.keys()):
            if not isinstance(key, str):
                raise TypeError("Python dict key is not Janus atom-compatible")
            items.append([key, encode_value(value[key])])
        return tagged("mapping", "items", items)
    if isinstance(value, Iterator):
        return tagged("list", "items", [encode_value(item) for item in value])
    if isinstance(value, Sequence):
        return tagged("list", "items", [encode_value(item) for item in value])
    return tagged("handle", "id", opaque_handle(value))


def invoke(spec, encoded_args):
    args = [decode_value(arg) for arg in encoded_args]
    if spec.startswith("."):
        if not args:
            raise TypeError(f"{spec} requires a receiver")
        target, *positional = args
        action = getattr(target, spec[1:])
    elif spec.count(".") == 1:
        module_name, function_name = spec.split(".", 1)
        target = importlib.import_module(module_name)
        action = getattr(target, function_name)
        positional = args
    else:
        action = getattr(builtins, spec)
        positional = args
    if callable(action):
        return action(*positional)
    if positional:
        raise TypeError(f"Python attribute {spec} is not callable")
    return action


def invoke_with_fixture(spec, encoded_args):
    if call_fixture is None:
        return invoke(spec, encoded_args)
    cursor = call_fixture["cursor"]
    responses = call_fixture["responses"]
    if cursor < len(responses) and responses[cursor].get("spec") == spec:
        entry = responses[cursor]
        call_fixture["cursor"] = cursor + 1
        if "error" in entry:
            raise RuntimeError(str(entry["error"]))
        return decode_value(entry["value"])
    if spec in call_fixture["allow"]:
        return invoke(spec, encoded_args)
    expected = responses[cursor].get("spec") if cursor < len(responses) else None
    raise PermissionError(
        f"Python call is not fixture-authorized: {spec}; next={expected}")


def import_module(module_name, module_path):
    if not module_path:
        importlib.import_module(module_name)
        return "true"
    absolute = os.path.abspath(module_path)
    directory = os.path.dirname(absolute)
    if directory not in sys.path:
        sys.path.append(directory)
    spec = importlib.util.spec_from_file_location(module_name, absolute)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load Python module {module_name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return "true"


def _load_prolog():
    """Load the sibling SWI-Prolog worker module as the single Prolog authority
    (its `solve` renders a goal to swipl and parses the ordered answer bag)."""
    import importlib.util
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "pleatta-prolog-worker.py")
    spec = importlib.util.spec_from_file_location("pleatta_prolog_worker", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_prolog = None


def _prolog_term(term):
    """PrologTerm JSON ({"var":{"name"}}|{"int":{"value"}}|...) -> solve() term."""
    tag, payload = next(iter(term.items()))
    if tag == "var":
        return {"var": payload["name"]}
    if tag == "int":
        return {"int": payload["value"]}
    if tag == "floating":
        return {"float": payload["bits"]}
    if tag == "atom":
        return {"atom": payload["name"]}
    if tag == "str":
        return {"str": payload["value"]}
    if tag == "list":
        return {"list": [_prolog_term(a) for a in payload["items"]]}
    if tag == "compound":
        return {"compound": [payload["functor"],
                             *[_prolog_term(a) for a in payload["args"]]]}
    if tag == "resource":
        raise TypeError("host resource cannot enter the generic Prolog worker")
    raise TypeError(f"unsupported PrologTerm {tag}")


def _prolog_hostvalue(value):
    """solve() answer value ({"int"}|{"float"}|{"atom"}) -> HostValue JSON."""
    if "int" in value:
        return tagged("integer", "value", value["int"])
    if "float" in value:
        return tagged("floating", "bits", str(value["float"]))
    if "atom" in value:
        return tagged("string", "value", value["atom"])
    if "str" in value:
        return tagged("string", "value", value["str"])
    raise TypeError("unsupported Prolog answer value")


def prolog_call(payload, module_path=None):
    """Evaluate one translatePredicate-lowered goal; PLeaTTa threads bindings, so
    this stays stateless -- a single answer substitution is returned as a mapping."""
    global _prolog
    if _prolog is None:
        _prolog = _load_prolog()
    libraries = []
    if module_path:
        libraries.append(_rooted_path(module_path))
    out = _prolog.solve({
        "goal": payload["functor"],
        "args": [_prolog_term(a) for a in payload.get("args", [])],
        "vars": payload.get("vars", []),
        "libraries": libraries,
    })
    if "error" in out:
        raise RuntimeError(f"prolog:{out['error']}")
    answers = out.get("answers", [])
    if not answers:
        return "failed"
    items = [[key, _prolog_hostvalue(val)] for key, val in answers[0].items()]
    return {"returned": {"value": tagged("mapping", "items", items)}}


def _host_number(encoded):
    tag, payload = next(iter(encoded.items()))
    if tag == "integer":
        return float(payload["value"])
    if tag == "floating":
        return struct.unpack(">d", struct.pack(">Q", int(payload["bits"])))[0]
    raise TypeError("invalid HostNumber")


def _rooted_path(logical):
    root = os.environ.get("PLEATTA_HOST_ROOT", "")
    if not root:
        raise PermissionError("file host effects require PLEATTA_HOST_ROOT")
    root = os.path.realpath(root)
    raw = str(logical)
    candidate = raw if os.path.isabs(raw) else os.path.join(root, raw)
    resolved = os.path.realpath(candidate)
    try:
        inside = os.path.commonpath([root, resolved]) == root
    except ValueError:
        inside = False
    if not inside:
        raise PermissionError("file host path escapes the configured root")
    return resolved


def _mapping(items=()):
    return tagged("mapping", "items", list(items))


def _resource(kind, resource_id):
    return {"resource": {"kind": kind, "id": resource_id}}


def _allocate_resource(kind, value):
    global next_resource
    resource_id = next_resource
    next_resource += 1
    resources[(kind, resource_id)] = value
    return resource_id


def _file_handle(resource_id):
    key = ("file", int(resource_id))
    if key not in resources:
        raise ReferenceError(f"unknown file resource {resource_id}")
    return resources[key]


def host_effect(operation):
    """Execute one typed effect and return an encoded HostValue."""
    if operation == "clock":
        return tagged("floating", "bits", float_bits(time.time()))
    if not isinstance(operation, dict) or len(operation) != 1:
        raise TypeError("malformed HostEffect")
    tag, payload = next(iter(operation.items()))
    if tag == "sleep":
        duration = _host_number(payload["duration"])
        maximum = float(os.environ.get("PLEATTA_MAX_SLEEP_SECONDS", "5"))
        if duration < 0 or duration > maximum:
            raise ValueError("sleep duration is outside the allowed bound")
        time.sleep(duration)
        return _mapping()
    if tag == "fileExists":
        if not os.path.exists(_rooted_path(payload["path"])):
            raise FileNotFoundError("logical host path does not exist")
        return _mapping()
    if tag == "fileRead":
        with open(_rooted_path(payload["path"]), encoding="utf-8") as handle:
            value = handle.read()
        return _mapping([[payload["resultVar"], encode_value(value)]])
    if tag == "fileOpen":
        modes = {"read": "r", "write": "w", "append": "a"}
        mode = payload["mode"]
        if mode not in modes:
            raise ValueError("unsupported file mode")
        path = _rooted_path(payload["path"])
        if mode in {"write", "append"}:
            os.makedirs(os.path.dirname(path), exist_ok=True)
        handle = open(path, modes[mode], encoding="utf-8")
        resource_id = _allocate_resource("file", handle)
        return _mapping([[payload["resultVar"], _resource("file", resource_id)]])
    if tag == "fileWrite":
        handle = _file_handle(payload["handle"])
        handle.write(payload["text"])
        handle.flush()
        return _mapping()
    if tag == "fileNewline":
        handle = _file_handle(payload["handle"])
        handle.write("\n")
        handle.flush()
        return _mapping()
    if tag == "fileClose":
        resource_id = int(payload["handle"])
        handle = _file_handle(resource_id)
        handle.close()
        del resources[("file", resource_id)]
        return _mapping()
    if tag == "formatTime":
        stamp = payload.get("stamp")
        instant = time.time() if stamp is None else _host_number(stamp)
        value = time.strftime(payload["format"], time.localtime(instant))
        return _mapping([[payload["resultVar"], encode_value(value)]])
    raise TypeError(f"unsupported HostEffect {tag}")


def dispatch(command):
    request = command["request"]
    if "call" in request:
        payload = request["call"]
        result = invoke_with_fixture(payload["spec"], payload["args"])
    elif "importModule" in request:
        payload = request["importModule"]
        result = import_module(payload["name"], command.get("modulePath"))
    elif "prologCall" in request:
        return prolog_call(request["prologCall"], command.get("modulePath"))
    elif "effect" in request:
        payload = request["effect"]
        operation = payload.get("operation", payload)
        return {"returned": {"value": host_effect(operation)}}
    else:
        raise TypeError("unknown HostRequest")
    return {"returned": {"value": encode_value(result)}}


def reply(command):
    try:
        response = dispatch(command)
    except BaseException as error:
        response = {
            "raised": {
                "error": {
                    "kind": type(error).__name__,
                    "message": str(error),
                }
            }
        }
    return {"id": command.get("id", 0), "response": response}


def reserve_protocol_stdout():
    """Reserve the inherited stdout pipe for JSON and redirect host output.

    Imported modules may print from the request thread or from background
    threads.  Duplicating the protocol descriptor before redirecting fd 1
    keeps both Python-level and native-extension stdout away from the JSON
    stream.  The parent inherits stderr, so diagnostics are continuously
    drained instead of filling an unread pipe.
    """
    sys.stdout.flush()
    protocol = os.fdopen(
        os.dup(sys.stdout.fileno()), "w", buffering=1, encoding="utf-8")
    os.dup2(sys.stderr.fileno(), sys.stdout.fileno())
    sys.stdout = sys.stderr
    return protocol


def main():
    protocol = reserve_protocol_stdout()
    host_root = os.environ.get("PLEATTA_HOST_ROOT", "")
    if host_root:
        os.chdir(os.path.realpath(host_root))
    try:
        for line in sys.stdin:
            try:
                command = json.loads(line)
                result = reply(command)
            except BaseException as error:
                result = {
                    "id": 0,
                    "response": {
                        "raised": {
                            "error": {
                                "kind": type(error).__name__,
                                "message": str(error),
                            }
                        }
                    },
                }
            protocol.write(json.dumps(result, separators=(",", ":")) + "\n")
            protocol.flush()
    finally:
        for resource in list(resources.values()):
            close = getattr(resource, "close", None)
            if close is not None:
                close()
        resources.clear()


if __name__ == "__main__":
    main()
