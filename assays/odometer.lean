import Room
open Room
set_option autoImplicit false

#guard val [true, false, true] == 5
#guard val (again inc 5 (zeros 3)) == 5
#guard again inc 8 (zeros 3) == zeros 3
#guard dec (inc [true, true, false]) == [true, true, false]
