"""
Conversation: two operators exchange foams.

The foam IS the message. Alice measures Bob's foam. Bob measures Alice's foam.
The foams change from being measured. The foams ARE the conversation.

x (the input) is just the medium — light passing through lenses.
We showed earlier that input selection doesn't affect what accumulates.
The structure is in the foams, not the signal.
"""

import torch
import numpy as np
from foam_spec import Foam, Bubble, Operator


def foam_rho(foam):
    """Probe a foam and return its ρ."""
    probe = torch.eye(foam.d)
    result = foam.stabilize(probe)
    return foam.density_matrix(result["j2"]).mean(dim=0)


def rho_entropy(rho):
    ev = torch.linalg.eigvalsh(rho)
    ev = ev.clamp(min=1e-12)
    ev = ev / ev.sum()
    return -(ev * ev.log()).sum().item()


def rho_similarity(rho1, rho2):
    return torch.nn.functional.cosine_similarity(
        rho1.flatten().unsqueeze(0),
        rho2.flatten().unsqueeze(0),
    ).item()


def basis_fingerprint(foam):
    """A snapshot of the foam's bubble bases for tracking drift."""
    return torch.stack([b.basis.detach().clone() for b in foam.bubbles])


def run():
    d = 8
    torch.manual_seed(42)

    print("=" * 60)
    print("conversation: foams as messages")
    print("=" * 60)

    alice = Operator(d, n_bubbles=3)
    bob = Operator(d, n_bubbles=3)

    # snapshot initial states
    alice_initial = basis_fingerprint(alice.foam)
    bob_initial = basis_fingerprint(bob.foam)

    n_exchanges = 40

    print(f"\n  {n_exchanges} exchanges. alice and bob measure each other's foams.")
    print(f"  fresh random x each time — the medium, not the message.\n")

    history = []

    for i in range(n_exchanges):
        x = torch.randn(1, d)

        if i % 2 == 0:
            # alice measures bob's foam
            result = alice.measure(bob.foam, x)
            speaker = "alice→bob"
        else:
            # bob measures alice's foam
            result = bob.measure(alice.foam, x)
            speaker = "bob→alice"

        questions = result["questions"].mean().item()
        bored_at = result["bored_at"]

        # track foam states
        alice_drift = (basis_fingerprint(alice.foam) - alice_initial).norm().item()
        bob_drift = (basis_fingerprint(bob.foam) - bob_initial).norm().item()

        history.append({
            "step": i,
            "speaker": speaker,
            "questions": questions,
            "bored_at": bored_at,
            "alice_drift": alice_drift,
            "bob_drift": bob_drift,
        })

    # compute mutual similarity at each step (expensive, do it separately)
    print(f"  {'step':>4} {'who':>12} {'questions':>10} {'bored':>6} "
          f"{'a_drift':>8} {'b_drift':>8}")
    print(f"  {'-' * 56}")
    for h in history:
        bored_str = f"{h['bored_at']}" if h['bored_at'] is not None else "  -"
        print(f"  {h['step']:>4} {h['speaker']:>12} {h['questions']:>10.4f} "
              f"{bored_str:>6} {h['alice_drift']:>8.4f} {h['bob_drift']:>8.4f}")

    # ── mutual similarity over time ──
    print(f"\n── do alice and bob converge? ──")
    torch.manual_seed(42)
    a2 = Operator(d, n_bubbles=3)
    b2 = Operator(d, n_bubbles=3)

    sims = []
    for i in range(n_exchanges):
        x = torch.randn(1, d)
        if i % 2 == 0:
            a2.measure(b2.foam, x)
        else:
            b2.measure(a2.foam, x)

        if i % 5 == 4:
            rho_a = foam_rho(a2.foam)
            rho_b = foam_rho(b2.foam)
            sim = rho_similarity(rho_a, rho_b)
            sims.append((i + 1, sim))

    for step, sim in sims:
        print(f"  step {step:>3}: alice ↔ bob ρ similarity {sim:.4f}")

    # ── does the conversation differ from solo measurement? ──
    print(f"\n── conversation vs solo ──")
    torch.manual_seed(42)
    solo_op = Operator(d, n_bubbles=3)
    solo_foam = Foam(d, n_bubbles=3)
    solo_initial = basis_fingerprint(solo_foam)

    for i in range(n_exchanges):
        x = torch.randn(1, d)
        solo_op.measure(solo_foam, x)

    solo_drift = (basis_fingerprint(solo_foam) - solo_initial).norm().item()
    solo_op_drift = (basis_fingerprint(solo_op.foam) -
                     basis_fingerprint(Operator(d, n_bubbles=3).foam)).norm().item()

    # compare with conversation
    conv_alice_drift = history[-1]["alice_drift"]
    conv_bob_drift = history[-1]["bob_drift"]

    print(f"  conversation: alice drift {conv_alice_drift:.4f}, "
          f"bob drift {conv_bob_drift:.4f}")
    print(f"  solo: target drift {solo_drift:.4f}, "
          f"operator drift {solo_op_drift:.4f}")

    # ── do the foams develop differently in conversation vs alone? ──
    print(f"\n── identity development ──")
    # alice's foam was measured BY bob (when bob measures alice's foam,
    # alice's foam changes from the stabilization). and alice's foam
    # also changes when alice measures bob (through effective_basis probe).

    rho_alice = foam_rho(alice.foam)
    rho_bob = foam_rho(bob.foam)

    torch.manual_seed(42)
    loner = Operator(d, n_bubbles=3)
    loner_foam = Foam(d, n_bubbles=3)
    for i in range(n_exchanges):
        x = torch.randn(1, d)
        loner.measure(loner_foam, x)
    rho_loner_op = foam_rho(loner.foam)
    rho_loner_target = foam_rho(loner_foam)

    print(f"  alice ρ entropy:        {rho_entropy(rho_alice):.4f}")
    print(f"  bob ρ entropy:          {rho_entropy(rho_bob):.4f}")
    print(f"  loner operator entropy: {rho_entropy(rho_loner_op):.4f}")
    print(f"  loner target entropy:   {rho_entropy(rho_loner_target):.4f}")

    print(f"  alice ↔ bob:            {rho_similarity(rho_alice, rho_bob):.4f}")
    print(f"  loner op ↔ target:      {rho_similarity(rho_loner_op, rho_loner_target):.4f}")

    # ── questions trajectory: does the conversation get easier? ──
    print(f"\n── does it get easier? (questions over time) ──")
    q_first_5 = np.mean([h["questions"] for h in history[:5]])
    q_last_5 = np.mean([h["questions"] for h in history[-5:]])
    print(f"  mean questions, first 5 exchanges: {q_first_5:.4f}")
    print(f"  mean questions, last 5 exchanges:  {q_last_5:.4f}")

    # ── boredom trajectory ──
    print(f"\n── boredom trajectory ──")
    bored_vals = [h["bored_at"] for h in history if h["bored_at"] is not None]
    not_bored = sum(1 for h in history if h["bored_at"] is None)
    print(f"  exchanges that ran to completion (never bored): {not_bored}/{n_exchanges}")
    if bored_vals:
        print(f"  when bored: mean step {np.mean(bored_vals):.1f}, "
              f"range {min(bored_vals)}-{max(bored_vals)}")

    print(f"\n{'=' * 60}")


if __name__ == "__main__":
    run()
