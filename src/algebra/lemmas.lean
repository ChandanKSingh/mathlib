import algebra.module
import algebra.pi_instances

-- TODO: move
lemma is_linear_map_add {α β : Type*} [ring α] [add_comm_group β] [module α β]:
  is_linear_map α (λ (x : β × β), x.1 + x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp },
  { intros x y,
    simp [smul_add] }
end

-- TODO: move
lemma is_linear_map_sub {α β : Type*} [ring α] [add_comm_group β] [module α β]:
  is_linear_map α (λ (x : β × β), x.1 - x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp },
  { intros x y,
    simp [smul_add] }
end
