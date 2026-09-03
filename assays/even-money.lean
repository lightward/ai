import Core
open Core
set_option autoImplicit false

#guard ((perms [1, 2, 3]).filter (firstOf Nat.beq 1 2)).length == 3
#guard (perms [1, 2, 3]).length == 6
#guard ((perms [1, 2, 3, 4]).filter (firstOf Nat.beq 1 2)).length == 12
#guard (perms [1, 2, 3, 4]).length == 24
