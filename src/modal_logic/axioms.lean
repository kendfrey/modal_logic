import modal_logic.tactic

universes u

class is_dense (α : Type u) (r : α → α → Prop) : Prop :=
(dense : ∀ a b, r a b → ∃ c, r a c ∧ r c b)

class is_serial (α : Type u) (r : α → α → Prop) : Prop :=
(serial : ∀ a, ∃ b, r a b)

namespace modal_logic

open modal_logic

variables [modal_model : modal_model] (w : World) (p q : MProp)

lemma of : w ⊩ p ⇒ q → w ⊩ p → w ⊩ q :=
  by simp only [sat_imp, imp_self]

lemma em : w ⊩ p ∨ ¬p :=
  by simp only [modal_prop.or, sat_imp, imp_self]

lemma nec_imp_nec_of_nec_imp : w ⊩ □(p ⇒ q) ⇒ □p ⇒ □q :=
begin
  m.intros h h' v h_v,
  m.apply h,
  {
    apply h_v,
  },
  {
    m.apply h',
    apply h_v,
  },
end

lemma of_nec [is_refl World (≺)] : w ⊩ □p ⇒ p :=
begin
  m.intros h,
  m.apply h,
  m.apply refl,
end

lemma nec_nec_of_nec [is_trans World (≺)] : w ⊩ □p ⇒ □□p :=
begin
  m.intros h v h_v u h_u,
  m.apply h,
  apply trans h_v h_u,
end

lemma nec_of_nec_nec [is_dense World (≺)] : w ⊩ □□p ⇒ □p :=
begin
  m.intros h v h_v,
  rcases is_dense.dense w v h_v with ⟨u, h_u, h_u'⟩,
  m.apply_nec _ using h_u',
  m.apply_nec h using h_u,
end

lemma poss_of_nec [is_serial World (≺)] : w ⊩ □p ⇒ ◇p :=
begin
  m.intros h,
  rcases @is_serial.serial World (≺) _ w with ⟨v, h_v⟩,
  m.use [v, h_v],
  m.apply h,
  apply h_v,
end

lemma nec_poss [is_symm World (≺)] : w ⊩ p ⇒ □◇p :=
begin
  m.intros h v h_v,
  m.use [w, symm h_v],
  m.apply h,
end

end modal_logic