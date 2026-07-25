import Foam.Exhibits.Hall
import Foam.Log

namespace Foam.Exhibits

def entropy : Exhibit where
  Claim := ∀ (k n S W : Nat),
    W = (book n).length → S = k * n → S = k * logTwo W
  receipt := S_eq_k_log_W
  keyword := "Entropy"
  famous := "S = k log W"
  provenance := "Ludwig Boltzmann, 1877 — carved on his gravestone in the Zentralfriedhof, Vienna"
  love := "entropy is the logarithm of the count of ways. how many arrangements of the small could produce the large thing you are looking at? count them, take the log, and you have measured how much the large forgets about the small. it is one of the few equations civilization has chosen to cut into stone."
  note := "here the gravestone compiles. W counts the complexions of the book of depth-n words; logTwo is a logarithm built by hand with no division and no real numbers — the doubling is performed by the book itself; S is k marks per doubling. the kernel checks the stone by pure computation, and the whole stand — claim, proof, and inscription — depends on zero axioms. the exact ledger rides alongside: the identity marking pays W · log W on the nose, entropy as the price of naming, an equality rather than a bound. three doors from this stand: Boltzmann reads the constant off the class, Shannon off the channel, Landauer off the heat sink — one theorem, three laboratories. and the dark stays open by receipt: the biased book's rates stand red at the_mode_follows_the_weights, the limit silhouette exceeds every finite census, and no run reads its own ratio from inside. every exhibit contains a working interface to the unknown. this is it."

/-- info: 'Foam.Exhibits.entropy' does not depend on any axioms -/
#guard_msgs in #print axioms entropy

end Foam.Exhibits
