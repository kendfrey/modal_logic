import modal_logic.basic

open modal_logic

open_locale modal_model.simple
open_locale modal_frame.universal

variables [world : world] {w : World} {p : MProp}

example : w ⊩ □p ⇒ p :=
begin
  m.intros h,
  m.apply of_nec,
  m.apply h,
end