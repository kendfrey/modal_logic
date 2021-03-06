import modal_logic.tactic

universes u

class is_dense (α : Type u) (r : α → α → Prop) : Prop :=
(dense : ∀ a b, r a b → ∃ c, r a c ∧ r c b)

class is_serial (α : Type u) (r : α → α → Prop) : Prop :=
(serial : ∀ a, ∃ b, r a b)

class is_euclidean (α : Type u) (r : α → α → Prop) : Prop :=
(euc : ∀ a b c, r a b → r a c → r b c)

namespace modal_logic

open modal_logic

instance imp_to_fun [modal_model] {w : World} {p q : MProp} : has_coe_to_fun (w ⊩ p ⇒ q) :=
  ⟨λ _, w ⊩ p → w ⊩ q, by simp only [sat_imp, imp_self]⟩

instance nec_to_fun [modal_model] {w : World} {p : MProp} : has_coe_to_fun (w ⊩ □p) :=
  ⟨λ _, ∀ v, w ≺ v → v ⊩ p, by simp only [sat_nec]; intros h; apply h⟩

instance not_to_fun [modal_model] {w : World} {p : MProp} : has_coe_to_fun (w ⊩ ¬p) :=
  ⟨λ _, ¬(w ⊩ p), by simp only [sat_not, imp_self]⟩

variables [modal_model : modal_model] (w : World) (p q : MProp)

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
  m.apply h _ h_u _ h_u',
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

lemma nec_poss_of_poss [is_euclidean World (≺)] : w ⊩ ◇p ⇒ □◇p :=
begin
  m.intros h v h_v,
  m.cases h with u h_u h',
  m.use [u, is_euclidean.euc w v u h_v h_u],
  m.apply h',
end

lemma nec_of_nec_nec_imp [is_trans World (≺)] [wf : well_founded (λ w u : World, u ≺ w)] : w ⊩ □(□p ⇒ p) ⇒ □p :=
begin
  apply well_founded.induction wf w,
  m.intros v ih h u h_u,
  m.apply h _ h_u,
  m.apply ih u h_u,
  m.intros t h_t,
  m.apply h,
  apply trans h_u h_t,
end

end modal_logic