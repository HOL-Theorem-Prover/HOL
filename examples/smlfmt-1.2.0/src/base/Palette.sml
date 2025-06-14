(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Palette =
struct

  structure TC = TerminalColors

  val green = TC.hsv {h = 120.0, s = 1.0, v = 0.75}
  val darkgreen = TC.hsv {h = 120.0, s = 0.8, v = 0.45}
  val red = TC.hsv {h = 0.0, s = 1.0, v = 0.65}
  val brightred = TC.hsv {h = 0.0, s = 1.0, v = 0.85}
  val yellow = TC.hsv {h = 60.0, s = 0.75, v = 0.65}
  val blue = TC.hsv {h = 240.0, s = 0.65, v = 0.85}
  val lightblue = TC.hsv {h = 180.0, s = 1.0, v = 0.75}
  val pink = TC.hsv {h = 300.0, s = 1.0, v = 0.75}
  val purple = TC.hsv {h = 269.0, s = 0.94, v = 1.0}
  val gray = TC.hsv {h = 0.0, s = 0.0, v = 0.55}
  val lightgray = TC.hsv {h = 0.0, s = 0.0, v = 0.95}
  val darkgray = TC.hsv {h = 0.0, s = 0.0, v = 0.05}

end
