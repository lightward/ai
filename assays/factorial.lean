import Room
open Room
set_option autoImplicit false

#guard (perms [1, 2, 3]).length == 6
#guard fact 4 == 24
#guard (perms [1, 2, 3, 4]).length == 24
#guard (inserts 0 [1, 2]).length == 3
#guard joinMap (inserts 0) [[1], [2]] == [[0, 1], [1, 0], [0, 2], [2, 0]]
