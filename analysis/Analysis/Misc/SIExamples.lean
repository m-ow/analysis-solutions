import Mathlib.Tactic
import Analysis.Misc.SI


namespace SI
open UnitsSystem


variable (m:Mass) (v:Speed) (F:Force) (p:Momentum) (E:Energy) (h:Length) (t:Time) (a:Acceleration)

#check F = m * a
#check p = m * v
#check h = v * t - g * t**2 / 2
#check E = m * c**2
#check E = m * v**2 / 2 + m * g * h
-- #check E = m * c**3  -- fails to typecheck
-- #check m + v -- fails to typecheck

example (hv : v = 60 • kilo meter / hour) : (StandardUnit _).in v = 50/(3:ℝ) := by
  simp [←Scalar.val_inj, hour, minute, kilo, meter, second, hv]
  norm_num

example (first_law : F = m * a) (hm : m = 2 • kilogram) (ha : a = 3 • meter / second**2) : F = 6 • newton := by
  simp [←Scalar.val_inj, first_law, hm, ha, kilogram, meter, second, newton]
  norm_num

example (kinetic: E = m * v**2 / 2) (hm : m = 2 • kilogram) (hv : v = 3 • meter / second) : joule.in E = 9 := by
  simp [←Scalar.val_inj, kinetic, hm, hv, kilogram, meter, second, joule]
  norm_num

example (ht : t = 3 • hour) : minute.in t = 180 := by
  simp [←Scalar.val_inj, hour, minute, ht]
  norm_num



end SI
