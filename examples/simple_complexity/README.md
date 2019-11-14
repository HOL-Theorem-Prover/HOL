# Algorithm Analysis

Investigation of the computational complexity analysis of algorithms
leads to the development of various underlying theories:

## Loop Recurrence
* __lib__ common library for basic notions of complexity.
    * `lib/bitsize`, bit size of number representations.
    * `lib/complexity`, big-O notation for complexity class.
    * `lib/recurrence`, recurrence theory for step counting loops.

* __loop__ library for patterns of loop recurrence.
    * `loop/loop`, general theory of loop recurrence, with body and exit.
    * `loop/loopIncrease`, recurrence theory of increasing loops.
    * `loop/loopDecrease`, recurrence theory of decreasing loops.
    * `loop/loopDivide`, recurrence theory of dividing loops.
    * `loop/loopMultiply`, recurrence theory of multiplying loops.
    * `loop/loopList`, recurrence theory of list reduction loops.
