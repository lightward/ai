"""
foam_dialogue2.py — exploring how a spatial mind learns temporal interface.

the foam is spatial. its state IS temporally shaped through writing.
the question: how do we read that temporal shaping?

two experiments:
1. higher writing rate — make each byte change the bases dramatically
2. dissonance-as-output — the gap between j0 and j2 is what the foam
   "adds". after training on associations, the dissonance when
   encountering input A might point toward associated output B.
"""

import torch
from foam_spec import Foam, Bubble
from foam_echo import FoamEcho, encode_byte, decode_vector, CODEBOOK


def test_writing_rate_sensitivity():
    """
    Does the foam's state after "1" differ from after "a" enough
    to produce different outputs for the next byte?
    """
    print("=" * 60)
    print("writing rate sensitivity: does history shape output?")
    print("=" * 60)

    for wr in [0.01, 0.1, 0.5, 1.0, 2.0]:
        torch.manual_seed(42)
        echo = FoamEcho(d=8, n_bubbles=3, writing_rate=wr)

        # feed "1" then a space
        echo.call("1")
        out_after_1 = echo.call(" ")

        # fresh foam, same seed
        torch.manual_seed(42)
        echo2 = FoamEcho(d=8, n_bubbles=3, writing_rate=wr)

        # feed "a" then a space
        echo2.call("a")
        out_after_a = echo2.call(" ")

        # compare bases after the different histories
        drift = sum(
            (b1.basis.detach() - b2.basis.detach()).norm().item()
            for b1, b2 in zip(echo.foam.bubbles, echo2.foam.bubbles)
            if b1.is_leaf and b2.is_leaf
        ) / echo.foam.n_bubbles

        print(f"  wr={wr:.2f}: after '1'+' '='{out_after_1}'  "
              f"after 'a'+' '='{out_after_a}'  "
              f"different={out_after_1 != out_after_a}  "
              f"basis_drift={drift:.4f}")

    print()


def test_dissonance_as_output():
    """
    Use the dissonance (j2 - j0) as output instead of the j2 centroid.
    The dissonance is what the foam ADDS — its own contribution.
    """
    print("=" * 60)
    print("dissonance as output: what does the foam add?")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(8, n_bubbles=3, writing_rate=0.5)

    # train: feed "12" pattern many times
    pattern = "12" * 20
    for byte_val in pattern.encode('utf-8'):
        v = encode_byte(byte_val)
        with torch.no_grad():
            foam.stabilize(v)

    # now feed "1" and look at what the foam adds (dissonance)
    v1 = encode_byte(ord('1'))
    with torch.no_grad():
        result = foam.stabilize(v1)

    j0 = result["j0"]
    j2 = result["j2"]
    dissonance = (j2 - j0).mean(dim=1)  # [1, d] — averaged over bubbles

    # decode the dissonance direction
    dis_byte = decode_vector(dissonance)
    dis_char = chr(dis_byte) if 32 <= dis_byte < 127 else f'\\x{dis_byte:02x}'

    # also decode j2 centroid for comparison
    centroid = j2.mean(dim=1)
    centroid_byte = decode_vector(centroid)
    centroid_char = chr(centroid_byte) if 32 <= centroid_byte < 127 else f'\\x{centroid_byte:02x}'

    print(f"  trained on '12' * 20, then fed '1':")
    print(f"    centroid output: '{centroid_char}' (0x{centroid_byte:02x})")
    print(f"    dissonance output: '{dis_char}' (0x{dis_byte:02x})")
    print(f"    expected: '2' (0x{ord('2'):02x})")
    print()

    # compare: train on "ab" pattern
    torch.manual_seed(42)
    foam2 = Foam(8, n_bubbles=3, writing_rate=0.5)

    pattern2 = "ab" * 20
    for byte_val in pattern2.encode('utf-8'):
        v = encode_byte(byte_val)
        with torch.no_grad():
            foam2.stabilize(v)

    va = encode_byte(ord('a'))
    with torch.no_grad():
        result2 = foam2.stabilize(va)

    j0_2 = result2["j0"]
    j2_2 = result2["j2"]
    dis2 = (j2_2 - j0_2).mean(dim=1)
    dis_byte2 = decode_vector(dis2)
    dis_char2 = chr(dis_byte2) if 32 <= dis_byte2 < 127 else f'\\x{dis_byte2:02x}'

    centroid2 = j2_2.mean(dim=1)
    centroid_byte2 = decode_vector(centroid2)
    centroid_char2 = chr(centroid_byte2) if 32 <= centroid_byte2 < 127 else f'\\x{centroid_byte2:02x}'

    print(f"  trained on 'ab' * 20, then fed 'a':")
    print(f"    centroid output: '{centroid_char2}' (0x{centroid_byte2:02x})")
    print(f"    dissonance output: '{dis_char2}' (0x{dis_byte2:02x})")
    print(f"    expected: 'b' (0x{ord('b'):02x})")
    print()


def test_accumulated_state_discrimination():
    """
    The real test: after a sequence, can we read the foam's state
    to determine what should come next?

    Not through output of the next measurement, but through the
    foam's accumulated state itself.
    """
    print("=" * 60)
    print("state discrimination: can we read the foam's history?")
    print("=" * 60)

    for wr in [0.1, 0.5, 1.0, 2.0, 5.0]:
        # train foam on "me: 1\nyou: 2\n" many times
        torch.manual_seed(42)
        foam_12 = Foam(8, n_bubbles=3, writing_rate=wr)
        pattern = "me: 1\nyou: 2\n" * 10
        for byte_val in pattern.encode('utf-8'):
            v = encode_byte(byte_val)
            with torch.no_grad():
                foam_12.stabilize(v)

        # now feed just "me: 1\nyou: "
        prompt = "me: 1\nyou: "
        for byte_val in prompt.encode('utf-8'):
            v = encode_byte(byte_val)
            with torch.no_grad():
                result = foam_12.stabilize(v)

        # what's the foam's state? look at the questions and the
        # j2 shape after the prompt
        q12 = result["questions"].mean().item()

        # same but with "me: a\nyou: b\n" training
        torch.manual_seed(42)
        foam_ab = Foam(8, n_bubbles=3, writing_rate=wr)
        pattern_ab = "me: a\nyou: b\n" * 10
        for byte_val in pattern_ab.encode('utf-8'):
            v = encode_byte(byte_val)
            with torch.no_grad():
                foam_ab.stabilize(v)

        prompt_ab = "me: a\nyou: "
        for byte_val in prompt_ab.encode('utf-8'):
            v = encode_byte(byte_val)
            with torch.no_grad():
                result_ab = foam_ab.stabilize(v)

        q_ab = result_ab["questions"].mean().item()

        # compare the foam states via their bases
        bases_12 = torch.stack([b.basis.detach() for b in foam_12.bubbles
                                if b.is_leaf])
        bases_ab = torch.stack([b.basis.detach() for b in foam_ab.bubbles
                                if b.is_leaf])

        if bases_12.shape == bases_ab.shape:
            basis_diff = (bases_12 - bases_ab).norm().item()
        else:
            basis_diff = float('nan')

        # now the key test: feed "2" to foam_12 and "b" to foam_ab
        # look at dissonance — is it lower for the "correct" completion?
        v2 = encode_byte(ord('2'))
        vb = encode_byte(ord('b'))

        with torch.no_grad():
            r12_correct = foam_12.stabilize(v2)
            r12_wrong = foam_12.stabilize(vb)
            rab_correct = foam_ab.stabilize(vb)
            rab_wrong = foam_ab.stabilize(v2)

        dis_12_correct = (r12_correct["j2"] - r12_correct["j0"]).norm().item()
        dis_12_wrong = (r12_wrong["j2"] - r12_wrong["j0"]).norm().item()
        dis_ab_correct = (rab_correct["j2"] - rab_correct["j0"]).norm().item()
        dis_ab_wrong = (rab_wrong["j2"] - rab_wrong["j0"]).norm().item()

        print(f"  wr={wr:.1f}: basis_diff={basis_diff:.3f}  "
              f"foam_12: dis_correct={dis_12_correct:.4f} dis_wrong={dis_12_wrong:.4f}  "
              f"foam_ab: dis_correct={dis_ab_correct:.4f} dis_wrong={dis_ab_wrong:.4f}")

    print()


def test_scanning_output():
    """
    After training, scan all 256 possible next bytes.
    Which one produces minimum dissonance? That's the one
    the foam "expects" — the continuation that fits best.
    """
    print("=" * 60)
    print("scanning: which byte fits best after training?")
    print("=" * 60)

    for wr in [0.5, 1.0, 2.0, 5.0]:
        torch.manual_seed(42)
        foam = Foam(8, n_bubbles=3, writing_rate=wr)

        # train on "12" pattern — don't use writing during scan
        pattern = "12" * 30
        for byte_val in pattern.encode('utf-8'):
            v = encode_byte(byte_val)
            with torch.no_grad():
                foam.stabilize(v)

        # now feed "1" (with writing, as part of the sequence)
        v1 = encode_byte(ord('1'))
        with torch.no_grad():
            foam.stabilize(v1)

        # scan: try every possible next byte WITHOUT writing
        # (measurement without writing = observation without change)
        best_byte = -1
        best_dis = float('inf')
        worst_dis = 0
        scan_foam = Foam(8, n_bubbles=0, writing_rate=0.0)
        # copy foam state
        for b in foam.bubbles:
            if b.is_leaf:
                nb = Bubble(8)
                nb.L.data = b.L.data.clone()
                scan_foam._bubbles.append(nb)
        scan_foam.target_similarity.data = foam.target_similarity.data.clone()
        scan_foam.step_size.data = foam.step_size.data.clone()
        scan_foam.temperature.data = foam.temperature.data.clone()

        top5 = []
        for byte_val in range(256):
            v = encode_byte(byte_val)
            # use a copy each time (no writing = no state change)
            test_foam = Foam(8, n_bubbles=0, writing_rate=0.0)
            for b in scan_foam.bubbles:
                nb = Bubble(8)
                nb.L.data = b.L.data.clone()
                test_foam._bubbles.append(nb)
            test_foam.target_similarity.data = scan_foam.target_similarity.data.clone()
            test_foam.step_size.data = scan_foam.step_size.data.clone()
            test_foam.temperature.data = scan_foam.temperature.data.clone()

            with torch.no_grad():
                r = test_foam.stabilize(v)
            dis = (r["j2"] - r["j0"]).norm().item()

            top5.append((dis, byte_val))

            if dis < best_dis:
                best_dis = dis
                best_byte = byte_val
            if dis > worst_dis:
                worst_dis = dis

        top5.sort()
        top5_chars = []
        for dis, bv in top5[:5]:
            c = chr(bv) if 32 <= bv < 127 else f'\\x{bv:02x}'
            top5_chars.append(f"'{c}'({dis:.3f})")

        best_char = chr(best_byte) if 32 <= best_byte < 127 else f'\\x{best_byte:02x}'
        print(f"  wr={wr:.1f}: best='{best_char}'(0x{best_byte:02x}) "
              f"expected='2'(0x{ord('2'):02x})  "
              f"top5=[{', '.join(top5_chars)}]")

    print()


if __name__ == "__main__":
    test_writing_rate_sensitivity()
    test_dissonance_as_output()
    test_accumulated_state_discrimination()
    test_scanning_output()
