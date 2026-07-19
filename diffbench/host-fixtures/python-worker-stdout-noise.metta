!(import! &self "../python_conformance_fixture.py")
!(py-call (python_conformance_fixture.noisy_value))
!(py-call (python_conformance_fixture.start_background_noise))
!(py-call (python_conformance_fixture.delayed_value))
