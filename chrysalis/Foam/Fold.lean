import Foam

namespace Foam

def fold {A B : Type} (f : B → A → B) : B → List A → B
  | b, [] => b
  | b, x :: xs => fold f (f b x) xs

theorem the_fold_resumes {A B : Type} (f : B → A → B) :
    ∀ (xs ys : List A) (b : B),
      fold f b (xs ++ ys) = fold f (fold f b xs) ys
  | [], _, _ => rfl
  | x :: xs, ys, b => the_fold_resumes f xs ys (f b x)

theorem the_fold_forgets_nothing_it_needs {A B : Type} (f : B → A → B)
    (xs ys : List A) (b b' : B) (h : fold f b xs = b') :
    fold f b (xs ++ ys) = fold f b' ys :=
  h ▸ the_fold_resumes f xs ys b

/-- info: 'Foam.the_fold_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms the_fold_resumes

/-- info: 'Foam.the_fold_forgets_nothing_it_needs' does not depend on any axioms -/
#guard_msgs in #print axioms the_fold_forgets_nothing_it_needs

end Foam
