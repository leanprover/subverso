-- This module deliberately contains errors, so it's not imported from Small. It exists to test the
-- extraction of code actions: the failing #guard_msgs offers its update action, and simp? offers a
-- "Try this" suggestion.

/-- info: wrong -/
#guard_msgs in
#eval 1 + 1

example : 1 + 1 = 2 := by simp?
