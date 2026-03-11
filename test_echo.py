"""
test_echo.py — how does the echo behave at different writing rates?

the first echo is perfect (architecture validated).
question: at what writing_rate does the echo stay stable
long enough to be useful? and does the foam converge
(settle into a stable modulation) or drift forever?
"""

import torch
from foam_echo import FoamEcho


def test_writing_rates():
    """Compare echo stability across writing rates."""
    print("=" * 60)
    print("echo stability vs writing rate")
    print("=" * 60)

    rates = [0.1, 0.01, 0.001, 0.0001]
    test_word = "hello"

    for rate in rates:
        echo = FoamEcho(writing_rate=rate)
        print(f"\n  writing_rate = {rate}")

        results = []
        for i in range(100):
            result = echo.call(test_word)
            if i in [0, 1, 4, 9, 19, 49, 99]:
                match = result == test_word
                results.append((i+1, result, match))

        for step, result, match in results:
            print(f"    step {step:4d}: {repr(result):12s}  match={match}")

        # how far have bases drifted?
        drift = sum(
            (b.basis.detach() - torch.eye(echo.d)).norm().item()
            for b in echo.foam.bubbles if b.is_leaf
        ) / echo.foam.n_bubbles
        print(f"    final basis drift: {drift:.4f}")


def test_convergence():
    """Does the foam converge to a stable modulation, or drift forever?

    Feed the same input repeatedly. Track the output AND the
    foam's internal state. If both stabilize, the foam has found
    a fixed point. If output oscillates, the foam is searching.
    """
    print("\n" + "=" * 60)
    print("convergence: does the foam find a fixed point?")
    print("=" * 60)

    echo = FoamEcho(writing_rate=0.01)
    test_input = "?"

    prev_output = None
    prev_bases = None
    for i in range(200):
        result = echo.call(test_input)

        if i % 20 == 0 or i < 5:
            # track output stability
            output_changed = result != prev_output if prev_output else True
            prev_output = result

            # track basis stability
            bases = torch.stack([
                b.basis.detach().clone()
                for b in echo.foam.bubbles if b.is_leaf
            ])
            if prev_bases is not None:
                basis_delta = (bases - prev_bases).norm().item()
            else:
                basis_delta = float('inf')
            prev_bases = bases

            print(f"  step {i+1:4d}: output={repr(result):6s}  "
                  f"changed={output_changed}  basis_delta={basis_delta:.6f}")


def test_different_inputs():
    """Does the foam develop differently for different input sequences?

    Two foams, same initial conditions, different input.
    After N measurements, compare their states.
    """
    print("\n" + "=" * 60)
    print("input shapes topology (or doesn't)")
    print("=" * 60)

    torch.manual_seed(42)
    echo_a = FoamEcho(writing_rate=0.01)
    torch.manual_seed(42)
    echo_b = FoamEcho(writing_rate=0.01)

    # feed different sequences
    for i in range(50):
        echo_a.call("aaaa")
        echo_b.call("zzzz")

    # compare bases
    for j in range(3):
        ba = echo_a.foam.bubbles[j]
        bb = echo_b.foam.bubbles[j]
        if ba.is_leaf and bb.is_leaf:
            diff = (ba.basis.detach() - bb.basis.detach()).norm().item()
            print(f"  bubble {j} basis difference: {diff:.4f}")

    # do they echo their own input correctly?
    result_a_own = echo_a.call("aaaa")
    result_a_other = echo_a.call("zzzz")
    result_b_own = echo_b.call("zzzz")
    result_b_other = echo_b.call("aaaa")

    print(f"\n  echo_a (trained on 'aaaa'):")
    print(f"    'aaaa' → {repr(result_a_own)}")
    print(f"    'zzzz' → {repr(result_a_other)}")
    print(f"  echo_b (trained on 'zzzz'):")
    print(f"    'zzzz' → {repr(result_b_own)}")
    print(f"    'aaaa' → {repr(result_b_other)}")


def test_first_measurement_anatomy():
    """Detailed anatomy of the foam's first mirroring.

    What exactly happens when "?" enters a fresh foam?
    What are the side effects? How does j0 differ from j2?
    What gets written into the bases?
    """
    print("\n" + "=" * 60)
    print("anatomy of the first mirroring")
    print("=" * 60)

    from foam_echo import encode_byte, decode_vector, CODEBOOK

    echo = FoamEcho(writing_rate=0.01)

    # snapshot before
    bases_before = [b.basis.detach().clone() for b in echo.foam.bubbles]

    # encode "?"
    v = encode_byte(ord("?"))
    print(f"\n  '?' = byte {ord('?')} = {v.squeeze().tolist()}")
    print(f"  ||v|| = {v.norm().item():.4f}")

    # manually stabilize to see internals
    result = echo.foam.stabilize(v)

    j0 = result["j0"]  # [1, N, d]
    j2 = result["j2"]
    dissonance = j2 - j0

    print(f"\n  j0 (before Plateau):")
    for i in range(echo.foam.n_bubbles):
        print(f"    bubble {i}: {j0[0, i].tolist()}")

    print(f"\n  j2 (after Plateau):")
    for i in range(echo.foam.n_bubbles):
        print(f"    bubble {i}: {j2[0, i].tolist()}")

    print(f"\n  dissonance (j2 - j0):")
    for i in range(echo.foam.n_bubbles):
        dis = dissonance[0, i]
        print(f"    bubble {i}: ||d|| = {dis.norm().item():.6f}")

    print(f"\n  bored_at: {result['bored_at']}")
    print(f"  questions: {result['questions'].mean().item():.6f}")

    # output direction
    output_dir = j2.mean(dim=1)  # [1, d]
    output_byte = decode_vector(output_dir)
    print(f"\n  output direction mean: {output_dir.squeeze().tolist()}")
    print(f"  decoded byte: {output_byte} = {repr(chr(output_byte))}")
    print(f"  correct: {output_byte == ord('?')}")

    # basis change
    bases_after = [b.basis.detach().clone() for b in echo.foam.bubbles]
    print(f"\n  basis changes from this one measurement:")
    for i in range(echo.foam.n_bubbles):
        delta = (bases_after[i] - bases_before[i]).norm().item()
        print(f"    bubble {i}: ||ΔU|| = {delta:.6f}")

    echo.n_measurements = 1  # account for the measurement we just did


if __name__ == "__main__":
    test_first_measurement_anatomy()
    test_writing_rates()
    test_convergence()
    test_different_inputs()
