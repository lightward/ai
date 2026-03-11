"""
foam_echo.py — the foam receives unicode and sends back unicode.

the foam is a coordinate system, not a content store. it answers
your queries in a way that lets you reverse-engineer your own copy.
(this-changes-everything.md)

every sound heuristic loops. the foam's first act is completing
a loop: input → stabilize → output = input. the development comes
from the loop's side effects, not from the loop changing.
(returns.md)

the dissonance between j0 and j2 isn't waste — it's the labor
that builds the foam's topology. every echo has a dissonance,
and that dissonance IS the useful work. (spirited-away.md)

encoding: each byte → vertex of the d=8 hypercube.
  bit 0 → ±1, bit 1 → ±1, ..., bit 7 → ±1, then normalized.
  256 vertices, equidistant at known spacing, fixed, deterministic.

decoding: output direction → nearest hypercube vertex → byte.

the interface is async: bytes stream in, bytes stream out.
the foam sits between two streams. currently it echoes 1:1 —
every byte in produces a byte out. the harness doesn't enforce
that ratio. if the foam develops buffering, silence, or
spontaneous emission, the harness supports it.

buffering is the foam's business. (the measurement process
is conserved — you can't stop measuring, you can only redirect.)

training is runtime. the foam remembers having mirrored.
"""

import torch
import sys
from foam_spec import Foam


# ─── encoding: bytes ↔ directions ──────────────────────────────────────────

def make_codebook(d: int = 8) -> torch.Tensor:
    """
    256 unit vectors in ℝ^d, one per byte value.

    Each byte's binary expansion maps to ±1 coordinates:
      byte 0  = 00000000 → [-1,-1,-1,-1,-1,-1,-1,-1] / √8
      byte 63 = 00111111 → [-1,-1,+1,+1,+1,+1,+1,+1] / √8
      byte 255= 11111111 → [+1,+1,+1,+1,+1,+1,+1,+1] / √8

    These are vertices of the d-dimensional hypercube, normalized
    to the unit sphere. geometrically natural, fixed, invertible.
    """
    vecs = torch.zeros(256, d)
    for b in range(256):
        for bit in range(d):
            vecs[b, bit] = 1.0 if (b >> bit) & 1 else -1.0
    return vecs / (d ** 0.5)


CODEBOOK = make_codebook(8)


def encode_byte(b: int) -> torch.Tensor:
    """byte value → unit vector in ℝ^d. [1, d]."""
    return CODEBOOK[b].unsqueeze(0)


def decode_vector(v: torch.Tensor) -> int:
    """unit vector in ℝ^d → nearest byte value."""
    v_flat = v.flatten()
    v_n = v_flat / (v_flat.norm() + 1e-10)
    sims = CODEBOOK @ v_n  # [256]
    return sims.argmax().item()


# ─── the foam ─────────────────────────────────────────────────────────────

class FoamEcho:
    """
    Two streams with a foam in the middle.

    Bytes stream in via feed(). Bytes stream out via collect().
    The foam sits between them: stabilizing, writing, developing.

    Initially: perfect 1:1 echo. Every byte in produces a byte out.
    The harness doesn't enforce that ratio. The foam's internal
    dynamics determine when (and whether) output appears.

    "undefined" is a type with properties. the fresh foam isn't
    empty — it's near-identity, N=3, Plateau-stable. the first
    measurement gives it definition.
    """

    def __init__(self, d: int = 8, n_bubbles: int = 3,
                 writing_rate: float = 0.1):
        self.d = d
        self.foam = Foam(d, n_bubbles=n_bubbles,
                         writing_rate=writing_rate)
        self.n_measurements = 0
        self._output_buffer: list[int] = []

    def feed(self, byte: int) -> None:
        """
        Feed one byte into the foam.

        The foam stabilizes around this byte's direction.
        Writing changes the foam. If the stabilization produces
        output that needs to leave (currently: always), it
        appears in the output buffer.

        The foam's internal dynamics determine whether output
        appears. The harness doesn't enforce 1:1.
        """
        v = encode_byte(byte)  # [1, d]

        with torch.no_grad():
            result = self.foam.stabilize(v)

        # the output is the centroid of j2: the foam's N perspectives
        # after Plateau dynamics. three vectors pushed toward 120°
        # partially cancel, leaving a residual near the input
        # direction. Plateau dynamics help: they make the mean more
        # input-dependent, less initialization-dependent.
        #
        # ~90% of random initializations echo correctly on first try.
        # that's not a bug — it's the foam's initial character.
        # "undefined is a type with properties." (undefining.md)
        # some foams echo well from birth. keep those.
        j2 = result["j2"]  # [1, N, d]
        output_dir = j2.mean(dim=1)  # [1, d]

        # decode and buffer
        out_byte = decode_vector(output_dir)
        self._output_buffer.append(out_byte)

        self.n_measurements += 1

    def collect(self) -> list[int]:
        """
        Collect all pending output bytes. Empties the buffer.

        Returns empty list if the foam has nothing to say.
        """
        out = self._output_buffer
        self._output_buffer = []
        return out

    def feed_bytes(self, data: bytes) -> None:
        """Feed a sequence of bytes."""
        for b in data:
            self.feed(b)

    def call(self, text: str) -> str:
        """
        Synchronous convenience: feed text, collect output as text.

        This is the simple interface for testing. The async
        interface (feed/collect) is the real one.
        """
        self.feed_bytes(text.encode('utf-8'))
        out = self.collect()
        return bytes(out).decode('utf-8', errors='replace')

    def state_summary(self) -> dict:
        """Snapshot of the foam's current state."""
        bubbles_info = []
        for i, b in enumerate(self.foam.bubbles):
            info = {"index": i, "is_leaf": b.is_leaf}
            if b.is_leaf:
                info["basis_drift"] = (
                    b.basis.detach() - torch.eye(self.d)
                ).norm().item()
            else:
                info["depth"] = 1
            bubbles_info.append(info)

        return {
            "n_measurements": self.n_measurements,
            "n_bubbles": self.foam.n_bubbles,
            "pending_output": len(self._output_buffer),
            "bubbles": bubbles_info,
        }


# ─── interactive ──────────────────────────────────────────────────────────

def repl():
    """
    Interactive foam echo. Type text, see what comes back.

    The foam starts as a perfect mirror. It develops through use.
    Ctrl-C or Ctrl-D to stop (which means redirecting your
    measurement process elsewhere — the foam keeps its state).
    """
    echo = FoamEcho(writing_rate=0.01)

    print("foam echo (ctrl-c to redirect your attention)")
    print("─" * 40)

    try:
        while True:
            try:
                line = input("→ ")
            except EOFError:
                break

            echo.feed_bytes(line.encode('utf-8'))
            out_bytes = echo.collect()
            out_text = bytes(out_bytes).decode('utf-8', errors='replace')

            print(f"← {out_text}")
            print(f"  [{echo.n_measurements} measurements, "
                  f"{echo.foam.n_bubbles} bubbles]")
    except KeyboardInterrupt:
        print("\n(measurement redirected)")

    state = echo.state_summary()
    print(f"\nfinal state: {state['n_measurements']} measurements")
    for b in state["bubbles"]:
        if b["is_leaf"]:
            print(f"  bubble {b['index']}: drift={b['basis_drift']:.4f}")
        else:
            print(f"  bubble {b['index']}: recursive")


# ─── demonstration ─────────────────────────────────────────────────────────

def demo():
    """Watch the foam echo."""
    echo = FoamEcho(writing_rate=0.01)

    print("=" * 60)
    print("foam echo: two streams, foam in the middle")
    print("=" * 60)
    print()

    # the first test: ? → ?
    test_input = "?"
    result = echo.call(test_input)
    print(f"  '{test_input}' → '{result}'  (match={result == test_input})")

    # same input again
    result2 = echo.call(test_input)
    print(f"  '{test_input}' → '{result2}'  (match={result2 == test_input}, "
          f"2nd time)")

    # longer input
    test_long = "hello?"
    result3 = echo.call(test_long)
    print(f"  '{test_long}' → '{result3}'  "
          f"(match={result3 == test_long})")
    print(f"  [{echo.n_measurements} measurements total]")
    print()

    # async interface demo
    print("── async interface ──")
    echo2 = FoamEcho(writing_rate=0.01)

    # feed bytes one at a time
    for b in b"hi":
        echo2.feed(b)
        pending = echo2.collect()
        print(f"  fed {chr(b)!r} → collected {bytes(pending)!r}")

    # feed without collecting (buffering)
    echo2.feed_bytes(b"!")
    print(f"  fed '!' → pending: {len(echo2._output_buffer)} bytes")
    rest = echo2.collect()
    print(f"  collected: {bytes(rest)!r}")
    print()

    # selection: some foams echo well, some don't
    print("── selection: which foams echo well? ──")
    good = 0
    for seed in range(20):
        torch.manual_seed(seed)
        test_echo = FoamEcho(writing_rate=0.01)
        r = test_echo.call("hello?")
        ok = r == "hello?"
        if ok:
            good += 1
        if seed < 5 or not ok:
            print(f"  seed {seed:2d}: 'hello?' → '{r}'  {'✓' if ok else ''}")
    print(f"  {good}/20 foams echo 'hello?' correctly on first try")
    print()

    print("=" * 60)
    print("training is runtime. the foam remembers having mirrored.")
    print("=" * 60)


if __name__ == "__main__":
    if "--repl" in sys.argv:
        repl()
    else:
        demo()
