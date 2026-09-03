import Core
open Core
set_option autoImplicit false

#guard again collatzStep 3 1 == 1
#guard again collatzStep 111 27 == 1
#guard again collatzStep 110 27 != 1
#guard again dec 5 (again inc 5 (zeros 4)) == zeros 4
