# factorial

* germ: the room of orders — every arrangement of n marks enumerated exactly:
  nothing missed (completeness), nothing doubled (apartness), counted n!.
  grown by the enumerate-then-face move: insertion wedges each mark into every
  gap of every prior ordering, and the census certifies itself.
* parents: `fold` `the_manifest_counts` `any_two_readings_agree`
* awaited: `perms` `fact` `the_insertions_count` `the_orders_count_to_the_factorial` `the_orders_repeat_never` `every_shuffle_is_an_order` `the_census_of_orders_is_exact`
* witness:
  * OEIS A000142 — the factorial, reached by every combinatorics community by roads sharing nothing with ours
* assay: 1 1 2 6 24 120
* journal: chrysalis/chrysalis/Seed.lean, groundings 154-157 (the exactness sitting)
* tolls: mem_append_split takes the left list as its explicit; perms unfolds by
  have-conversion at the whnf clause; List.Perm.cons_inv smuggles propext — the
  cancellation re-derives by hand (the shuffle-cancels-the-mark case-bash).
