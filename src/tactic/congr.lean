
import logic.basic

namespace tactic.interactive

setup_tactic_parser

open expr tactic

meta def apply_iff_congr_core (tgt : expr) : tactic unit :=
applyc ``iff_of_eq

meta def congr_core' : tactic unit :=
do tgt ← target,
   apply_eq_congr_core tgt
   <|> apply_heq_congr_core
   <|> apply_iff_congr_core tgt
   <|> fail "congr tactic failed"

/--
Same as the `congr` tactic, but takes an optional argument which gives
the depth of recursive applications. This is useful when `congr`
is too aggressive in breaking down the goal. For example, given
`⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`. -/
meta def congr' : parse (with_desc "n" small_nat)? → tactic unit
| (some 0) := failed
| o        := focus1 (assumption <|> (congr_core' >>
  all_goals (reflexivity <|> `[apply proof_irrel_heq] <|>
             `[apply proof_irrel] <|> try (congr' (nat.pred <$> o)))))


/--
Similar to `refine` but generates equality proof obligations
for every discrepancy between the goal and the type of the rule.
-/
meta def convert (sym : parse (with_desc "←" (tk "<-")?)) (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
do v ← mk_mvar,
   if sym.is_some
     then refine ``(eq.mp %%v %%r)
     else refine ``(eq.mpr %%v %%r),
   gs ← get_goals,
   set_goals [v],
   congr' n,
   gs' ← get_goals,
   set_goals $ gs' ++ gs

meta def clean_ids : list name :=
[``id, ``id_rhs, ``id_delta, ``hidden]

/--
Remove identity functions from a term. These are normally
automatically generated with terms like `show t, from p` or
`(p : t)` which translate to some variant on `@id t p` in
order to retain the type. -/
meta def clean (q : parse texpr) : tactic unit :=
do tgt : expr ← target,
   e ← i_to_expr_strict ``(%%q : %%tgt),
   tactic.exact $ e.replace (λ e n,
     match e with
     | (app (app (const n _) _) e') :=
       if n ∈ clean_ids then some e' else none
     | (app (lam _ _ _ (var 0)) e') := some e'
     | _ := none
     end)

meta def return_cast (f : option expr) (t : option (expr × expr))
  (es : list (expr × expr × expr))
  (e x x' eq_h : expr) :
  tactic (option (expr × expr) × list (expr × expr × expr)) :=
(do guard (¬ e.has_var),
    unify x x',
    u ← mk_meta_univ,
    f ← f <|> mk_mapp ``_root_.id [(expr.sort u : expr)],
    t' ← infer_type e,
    some (f',t) ← pure t | return (some (f,t'), (e,x',eq_h) :: es),
    infer_type e >>= is_def_eq t,
    unify f f',
    return (some (f,t), (e,x',eq_h) :: es)) <|>
return (t, es)

meta def list_cast_of_aux (x : expr) (t : option (expr × expr))
  (es : list (expr × expr × expr)) :
  expr → tactic (option (expr × expr) × list (expr × expr × expr))
| e@`(cast %%eq_h %%x') := return_cast none t es e x x' eq_h
| e@`(eq.mp %%eq_h %%x') := return_cast none t es e x x' eq_h
| e@`(eq.mpr %%eq_h %%x') := mk_eq_symm eq_h >>= return_cast none t es e x x'
| e@`(@eq.subst %%α %%p %%a %%b  %%eq_h %%x') := return_cast p t es e x x' eq_h
| e@`(@eq.substr %%α %%p %%a %%b %%eq_h %%x') := mk_eq_symm eq_h >>= return_cast p t es e x x'
| e@`(@eq.rec %%α %%a %%f %%x' _  %%eq_h) := return_cast f t es e x x' eq_h
| e@`(@eq.rec_on %%α %%a %%f %%b  %%eq_h %%x') := return_cast f t es e x x' eq_h
| e := return (t,es)

meta def list_cast_of (x tgt : expr) : tactic (list (expr × expr × expr)) :=
(list.reverse ∘ prod.snd) <$> tgt.mfold (none, []) (λ e i es, list_cast_of_aux x es.1 es.2 e)

private meta def h_generalize_arg_p_aux : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `heq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"

private meta def h_generalize_arg_p : parser (pexpr × name) :=
with_desc "expr == id" $ parser.pexpr 0 >>= h_generalize_arg_p_aux

/--
`h_generalize Hx : e == x` matches on `cast _ e` in the goal and replaces it with
`x`. It also adds `Hx : e == x` as an assumption. If `cast _ e` appears multiple
times (not necessarily with the same proof), they are all replaced by `x`. `cast`
`eq.mp`, `eq.mpr`, `eq.subst`, `eq.substr`, `eq.rec` and `eq.rec_on` are all treated
as casts.

`h_generalize Hx : e == x with h` adds hypothesis `α = β` with `e : α, x : β`.

`h_generalize Hx : e == x with _` chooses automatically chooses the name of
assumption `α = β`.

`h_generalize! Hx : e == x` reverts `Hx`.

when `Hx` is omitted, assumption `Hx : e == x` is not added.
-/
meta def h_generalize (rev : parse (tk "!")?)
     (h : parse ident_?)
     (_ : parse (tk ":"))
     (arg : parse h_generalize_arg_p)
     (eqs_h : parse ( (tk "with" >> pure <$> ident_) <|> pure [])) :
  tactic unit :=
do let (e,n) := arg,
   let h' := if h = `_ then none else h,
   h' ← (h' : tactic name) <|> get_unused_name ("h" ++ n.to_string : string),
   e ← to_expr e,
   tgt ← target,
   ((e,x,eq_h)::es) ← list_cast_of e tgt | fail "no cast found",
   interactive.generalize h' () (to_pexpr e, n),
   asm ← get_local h',
   v ← get_local n,
   hs ← es.mmap (λ ⟨e,_⟩, mk_app `eq [e,v]),
   (eqs_h.zip [e]).mmap' (λ ⟨h,e⟩, do
        h ← if h ≠ `_ then pure h else get_unused_name `h,
        () <$ note h none eq_h ),
   hs.mmap' (λ h,
     do h' ← assert `h h,
        tactic.exact asm,
        try (rewrite_target h'),
        tactic.clear h' ),
   when h.is_some (do
     (to_expr ``(heq_of_eq_rec_left %%eq_h %%asm)
       <|> to_expr ``(heq_of_eq_mp %%eq_h %%asm))
     >>= note h' none >> pure ()),
   tactic.clear asm,
   when rev.is_some (interactive.revert [n])

end tactic.interactive
