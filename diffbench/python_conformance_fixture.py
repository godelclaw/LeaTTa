class Box:
    def __init__(self, value):
        self.value = value


def integer_value():
    return 42


def floating_value():
    return -0.0


def string_value():
    return "Janus value"


def true_value():
    return True


def false_value():
    return False


def none_value():
    return None


def nested_list():
    return [1, [2, "x"], True, None]


def tuple_value():
    return (1, "x", False)


def mapping_value():
    return {"alpha": 1, "beta": "x"}


def make_box(value):
    return Box(value)


def identity(value):
    return value


def same_object(left, right):
    return left is right


def set_box(box, value):
    box.value = value
    return box


def get_box(box):
    return box.value


def raise_expected():
    raise ValueError("expected conformance failure")


def noisy_value():
    print("python worker foreground diagnostic", flush=True)
    return 41


def start_background_noise():
    import threading
    import time

    def emit():
        time.sleep(0.01)
        print("python worker background diagnostic", flush=True)

    threading.Thread(target=emit, daemon=True).start()
    return True


def delayed_value():
    import time
    time.sleep(0.05)
    return 42
