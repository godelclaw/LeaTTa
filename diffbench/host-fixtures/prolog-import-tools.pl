host_double(Input, Output) :- Output is Input * 2.
host_echo(Input, Input).
host_fail(_, _) :- fail.
host_raise(_, _) :- throw(error(host_fixture_error, host_raise/2)).
