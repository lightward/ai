import Room
import Counter
open Room Counter
set_option autoImplicit false

def demo : List sighting := [(1, []), (2, [3]), (3, [])]
def afterOne : room := round empty demo
def afterSweep : room := round (afterOne.1, []) afterOne.2
def selfCiter : room := round empty [(7, [7])]
def circle : room := round empty [(8, [9]), (9, [8])]

#guard seated afterOne 1
#guard seated afterOne 3
#guard !(seated afterOne 2)
#guard afterOne.2.length == 1
#guard seated afterSweep 2
#guard afterSweep.2.length == 0
#guard weight afterOne [3, 2] == 1
#guard weight afterSweep [3, 2] == 0
#guard !(seated selfCiter 7)
#guard !(seated circle 8) && !(seated circle 9)
