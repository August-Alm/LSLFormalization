import Formalization.QReads

/-!
# Pointer readback of a normal form

A closed, locally safe normal form reads back as itself with the pointer machine
(`normal_qreads`). The proof follows `reads_nf` for the token machine; the log takes the
place of the exponential stacks.
-/

namespace LSL

inductive Normal : Term → Prop
  | lam {A : Ty} {s : Term} : Normal s → Normal (.lam A s)
  | neu {x : Nat} {π : Path} {args : List Term} :
      (∀ u, u ∈ args → Normal u) → Normal (Term.apps (.var x π) args)

theorem normal_of_nostep : ∀ s : Term, (∀ s', ¬ Step s s') → Normal s
  | .var x π, _ => Normal.neu (x := x) (π := π) (args := []) (fun u hu => by simp at hu)
  | .lam A s, h => Normal.lam (normal_of_nostep s fun s' hs => h _ (Step.lam hs))
  | .app f u, h => by
    have hf := normal_of_nostep f fun f' hs => h _ (Step.appL hs)
    have hu := normal_of_nostep u fun u' hs => h _ (Step.appR hs)
    cases hf with
    | lam _ => exact absurd Step.beta (h _)
    | @neu x π args hargs =>
      have e : Term.app (Term.apps (.var x π) args) u = Term.apps (.var x π) (args ++ [u]) := by
        simp [Term.apps]
      rw [e]
      refine Normal.neu fun v hv => ?_
      rcases List.mem_append.mp hv with hv | hv
      · exact hargs v hv
      · simp only [List.mem_singleton] at hv
        subst hv
        exact hu

/-! ## Steps and walks -/

theorem qstep_app {t : Term} {a : Addr} {f u : Term} (h : t.sub a = some (.app f u))
    (T : List Item) (L : List Exit) :
    qstep t ⟨.down a, T, L⟩ = .next ⟨.down (.fn :: a), .q :: T, L⟩ := by
  simp [qstep, h]

theorem qstep_lam_q {t : Term} {a : Addr} {A : Ty} {b : Term} (h : t.sub a = some (.lam A b))
    (T : List Item) (L : List Exit) :
    qstep t ⟨.down a, .q :: T, L⟩ = .next ⟨.down (.body :: a), T, L⟩ := by
  simp [qstep, h]

theorem qstep_var {t : Term} {a : Addr} {i : Nat} {π : Path} {b : Addr}
    (h : t.sub a = some (.var i π)) (hb : binder a i = .inr b) (T : List Item)
    (L : List Exit) :
    qstep t ⟨.down a, T, L⟩ = .next ⟨.up b, .p ⟨a, L.take (argDepth a - argDepth b)⟩ :: T,
      L.drop (argDepth a - argDepth b)⟩ := by
  simp [qstep, h, hb]

theorem qstep_lam_p {t : Term} {a : Addr} {A : Ty} {b : Term} (h : t.sub a = some (.lam A b))
    {e : Exit} (he : binderOf t e.occ = some a) (T : List Item) (L : List Exit) :
    qstep t ⟨.down a, .p e :: T, L⟩ = .next ⟨.up e.occ, T, e.saved ++ L⟩ := by
  simp [qstep, h, he]

/-- The walk down a spine to its head. -/
theorem qspine {t : Term} : ∀ (args : List Term) (h : Term) (c : Addr),
    t.sub c = some (Term.apps h args) → ∀ (T : List Item) (L : List Exit),
      QR t ⟨.down c, T, L⟩
        ⟨.down (List.replicate args.length .fn ++ c), List.replicate args.length .q ++ T, L⟩
  | [], _, _, _, _, _ => QR.refl _ _
  | u :: rest, h, c, hs, T, L => by
    have hsub := (spine rest (.app h u) c hs).1
    exact (qspine rest (.app h u) c hs T L).trans (QR.one (qstep_app hsub _ L))

theorem qup_fn {t : Term} : ∀ (i : Nat) (c : Addr) (T : List Item) (L : List Exit),
    QR t ⟨.up (List.replicate i .fn ++ c), List.replicate i .q ++ T, L⟩ ⟨.up c, T, L⟩
  | 0, _, _, _ => QR.refl _ _
  | i + 1, c, T, L => by
    have h1 : qstep t ⟨.up (.fn :: (List.replicate i .fn ++ c)),
        .q :: (List.replicate i .q ++ T), L⟩ =
        .next ⟨.up (List.replicate i .fn ++ c), List.replicate i .q ++ T, L⟩ := rfl
    exact (QR.one h1).trans (qup_fn i c T L)

theorem argDepth_replicate_fn : ∀ (k : Nat) (a : Addr),
    argDepth (List.replicate k .fn ++ a) = argDepth a
  | 0, _ => rfl
  | k + 1, a => by
    show argDepth (.fn :: (List.replicate k .fn ++ a)) = _
    rw [argDepth_fn, argDepth_replicate_fn k a]

theorem replicate_mid {α : Type} (a : α) : ∀ (i j : Nat) (c : List α),
    List.replicate (i + (j + 1)) a ++ c = List.replicate i a ++ a :: (List.replicate j a ++ c)
  | 0, j, c => by
    rw [Nat.zero_add]
    rfl
  | i + 1, j, c => by
    rw [show i + 1 + (j + 1) = (i + (j + 1)) + 1 by omega]
    show a :: (List.replicate (i + (j + 1)) a ++ c) =
      a :: (List.replicate i a ++ a :: (List.replicate j a ++ c))
    rw [replicate_mid a i j c]

theorem tyAt_arity : ∀ (i : Nat) (C τ : Ty),
    tyAt C (List.replicate i .q ++ [.p]) = some τ → i < C.arity
  | 0, .o, τ, h => by simp [tyAt] at h
  | 0, .arr A B, τ, _ => by simp [Ty.arity]
  | i + 1, .o, τ, h => by simp [List.replicate_succ, tyAt] at h
  | i + 1, .arr A B, τ, h => by
    simp only [List.replicate_succ, List.cons_append, tyAt] at h
    have := tyAt_arity i B τ h
    simp only [Ty.arity]
    omega

/-! ## The walk up from an address, and back -/

/-- With the log `L`, the machine going up from `c` reaches the root with `W` on the tape,
and from the root with `W` on the tape it comes back down to `c`. -/
def QTop (t : Term) (c : Addr) (W : List Item) (L : List Exit) : Prop :=
  (∀ T, QR t ⟨.up c, T, L⟩ ⟨.up [], W ++ T, []⟩) ∧
    ∀ T, QR t ⟨.down [], W ++ T, []⟩ ⟨.down c, T, L⟩

theorem qtop_root (t : Term) : QTop t [] [] [] :=
  ⟨fun _ => QR.refl _ _, fun _ => QR.refl _ _⟩

theorem qtop_body {t : Term} {c : Addr} {W : List Item} {L : List Exit} {A : Ty} {s : Term}
    (h : QTop t c W L) (hsub : t.sub c = some (.lam A s)) :
    QTop t (.body :: c) (W ++ [.q]) L := by
  refine ⟨fun T => ?_, fun T => ?_⟩
  · have h1 : qstep t ⟨.up (.body :: c), T, L⟩ = .next ⟨.up c, .q :: T, L⟩ := rfl
    rw [List.append_assoc]
    exact (QR.one h1).trans (h.1 (.q :: T))
  · rw [List.append_assoc]
    exact (h.2 (.q :: T)).trans (QR.one (qstep_lam_q hsub T L))

/-- The argument of a head variable: on the way up the machine leaves through the variable,
and on the way down it comes back through it. -/
theorem qtop_arg {t : Term} {c : Addr} {x : Nat} {π : Path} {b : Addr} {W : List Item}
    {sv Lb : List Exit} (pre : List Term)
    (hfn : t.sub (.fn :: c) = some (Term.apps (.var x π) pre)) (hb : binder c x = .inr b)
    (hsv : sv.length = argDepth c - argDepth b) (htop : QTop t b W Lb) (d : Exit) :
    QTop t (.arg :: c)
      (W ++ .p ⟨List.replicate pre.length .fn ++ .fn :: c, sv⟩ ::
        (List.replicate pre.length .q ++ [.p d]))
      (d :: (sv ++ Lb)) := by
  obtain ⟨hhead, hbh⟩ := head_facts pre hfn hb
  have hdep : argDepth (List.replicate pre.length .fn ++ .fn :: c) - argDepth b = sv.length := by
    rw [argDepth_replicate_fn, argDepth_fn, hsv]
  have hbo : binderOf t (List.replicate pre.length .fn ++ .fn :: c) = some b := by
    simp [binderOf, hhead, hbh]
  obtain ⟨A, body, hlam, _⟩ := occ_mem hhead hbh
  have e : ∀ T : List Item,
      W ++ .p ⟨List.replicate pre.length .fn ++ .fn :: c, sv⟩ ::
        (List.replicate pre.length .q ++ [.p d]) ++ T =
      W ++ .p ⟨List.replicate pre.length .fn ++ .fn :: c, sv⟩ ::
        (List.replicate pre.length .q ++ .p d :: T) := by
    intro T
    simp
  refine ⟨fun T => ?_, fun T => ?_⟩
  · rw [e]
    have h1 : qstep t ⟨.up (.arg :: c), T, d :: (sv ++ Lb)⟩ =
        .next ⟨.down (.fn :: c), .p d :: T, sv ++ Lb⟩ := rfl
    have h2 := qspine pre _ _ hfn (.p d :: T) (sv ++ Lb)
    have h3 := qstep_var hhead hbh (List.replicate pre.length .q ++ .p d :: T) (sv ++ Lb)
    rw [hdep, List.take_left, List.drop_left] at h3
    exact (QR.one h1).trans (h2.trans ((QR.one h3).trans (htop.1 _)))
  · rw [e]
    have h1 := qstep_lam_p hlam (e := Exit.mk (List.replicate pre.length Dir.fn ++ .fn :: c) sv)
      hbo (List.replicate pre.length .q ++ .p d :: T) Lb
    have h2 := qup_fn (t := t) pre.length (.fn :: c) (.p d :: T) (sv ++ Lb)
    have h3 : qstep t ⟨.up (.fn :: c), .p d :: T, sv ++ Lb⟩ =
        .next ⟨.down (.arg :: c), T, d :: (sv ++ Lb)⟩ := rfl
    exact (htop.2 _).trans ((QR.one h1).trans (h2.trans (QR.one h3)))

/-! ## Readback of a normal form -/

/-- Every visible variable has a lambda whose tape `V ++ qˡ` at the root `resolve` maps back
to the variable; the log `L` at `c` is the log at that lambda with the entries for the
arguments in between in front. -/
def QVars (t : Term) (A₀ : Ty) (F : List Frame) (Γ : List Bind) (c : Addr) (L : List Exit) :
    Prop :=
  ∀ (x : Nat) (bnd : Bind), Γ[x]? = some bnd → bnd.zone ≠ .hid →
    ∃ (b : Addr) (V : List Item) (l : Nat) (sv Lb : List Exit) (body : Term),
      binder c x = .inr b ∧ t.sub b = some (.lam bnd.ty body) ∧
      L = sv ++ Lb ∧ sv.length = argDepth c - argDepth b ∧
      QTop t b (V ++ List.replicate l .q) Lb ∧
      resolve F (V.map Item.side) l = some x ∧
      dropQ (V.map Item.side).reverse = (0, (V.map Item.side).reverse) ∧
      tyAt A₀ (V.map Item.side ++ List.replicate l .q ++ [.p]) = some bnd.ty ∧
      (bnd.zone = .glob → V = [])

/-- `s` is the part of a point below its first `k` lambdas; the point has the tape `U`. -/
theorem qreads_nf {t : Term} {A₀ : Ty} {s : Term} (hnf : Normal s) :
    ∀ (m : Bool) (Γ : List Bind) (τ : Ty) (c : Addr) (anc : List Frame) (U : List Item)
      (k : Nat) (L : List Exit),
      LS m Γ s τ → t.sub c = some s → QTop t c (U ++ List.replicate k .q) L →
      (∀ k', k' < k → QStarved t ⟨.down [], U ++ List.replicate k' .q, []⟩) →
      dropQ (U.map Item.side).reverse = (0, (U.map Item.side).reverse) →
      tyAt A₀ (U.map Item.side ++ List.replicate k .q) = some τ →
      (m = false → U = []) →
      QVars t A₀ (⟨U.map Item.side, k⟩ :: anc) Γ c L →
      QReads t anc U (Tm.lams k (erase s)) := by
  induction hnf with
  | @lam A s' _ ih =>
    intro m Γ τ c anc U k L hls hsub htop hmin hU hty hroot hvars
    cases hls with
    | @lam _ _ _ B _ hbody =>
      have hsub' : t.sub (.body :: c) = some s' := by
        rw [sub_cons, hsub]
        rfl
      have htop' : QTop t (.body :: c) (U ++ List.replicate (k + 1) .q) L := by
        have h := qtop_body htop hsub
        rw [List.append_assoc, ← List.replicate_succ'] at h
        exact h
      have hmin' : ∀ k', k' < k + 1 →
          QStarved t ⟨.down [], U ++ List.replicate k' .q, []⟩ := by
        intro k' hk'
        by_cases hlt : k' < k
        · exact hmin k' hlt
        · have hk : k' = k := by omega
          rw [hk]
          have h1 := htop.2 []
          rw [List.append_nil] at h1
          exact h1.starved (.lam hsub)
      have hty' : tyAt A₀ (U.map Item.side ++ List.replicate (k + 1) .q) = some B := by
        rw [List.replicate_succ', ← List.append_assoc, tyAt_append, hty]
        simp [tyAt]
      have hvars' : QVars t A₀ (⟨U.map Item.side, k + 1⟩ :: anc) (⟨A, zoneOf m⟩ :: Γ)
          (.body :: c) L := by
        intro x bnd hx hz
        cases x with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          refine ⟨c, U, k, [], L, s', by simp [binder], hsub, rfl, by simp, htop,
            by simp [resolve], hU, ?_, ?_⟩
          · rw [tyAt_append, hty]
            simp [tyAt]
          · intro hg
            cases m with
            | true => simp [zoneOf] at hg
            | false => exact hroot rfl
        | succ y =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨b, V, l, sv, Lb, body, hb, hlam, hL, hsv, htb, hres, hV, htyb, hg⟩ :=
            hvars y bnd hx hz
          exact ⟨b, V, l, sv, Lb, body, by simpa [binder] using hb, hlam, hL,
            by simpa using hsv, htb, resolve_grow hres, hV, htyb, hg⟩
      have h := ih m _ B (.body :: c) anc U (k + 1) L hbody hsub' htop' hmin' hU hty' hroot
        hvars'
      rw [Tm.lams_succ'] at h
      exact h
  | @neu x π args _ ih =>
    intro m Γ τ c anc U k L hls hsub htop hmin hU hty hroot hvars
    obtain ⟨C, hC, hargs⟩ := ls_apps args (.var x π) m Γ τ hls
    cases hC with
    | @var _ _ _ _ bnd hx hz =>
      obtain ⟨b, V, l, sv, Lb, body, hbind, hlam, hL, hsv, htopb, hres, hV, htyb, hglob⟩ :=
        hvars x bnd hx hz
      subst hL
      have hhead := (spine args (.var x π) c hsub).1
      have hbh : binder (List.replicate args.length .fn ++ c) x = .inr b := by
        rw [binder_replicate_fn]
        exact hbind
      have hbo : binderOf t (List.replicate args.length .fn ++ c) = some b := by
        simp [binderOf, hhead, hbh]
      have hdep : argDepth (List.replicate args.length .fn ++ c) - argDepth b = sv.length := by
        rw [argDepth_replicate_fn, hsv]
      have hout : QOut t ⟨.down [], U ++ List.replicate k .q, []⟩
          (V ++ List.replicate l .q ++
            .p ⟨List.replicate args.length .fn ++ c, sv⟩ :: List.replicate args.length .q) := by
        have h1 := htop.2 []
        have h2 := qspine args (.var x π) c hsub [] (sv ++ Lb)
        have h3 := qstep_var hhead hbh (List.replicate args.length .q ++ []) (sv ++ Lb)
        rw [hdep, List.take_left, List.drop_left] at h3
        simp only [List.append_nil] at h1 h2 h3
        have h4 := htopb.1
          (.p ⟨List.replicate args.length .fn ++ c, sv⟩ :: List.replicate args.length .q)
        exact (h1.trans (h2.trans ((QR.one h3).trans h4))).out rfl
      have hlen : args.length ≤ bnd.ty.arity := by
        cases hlast : args[args.length - 1]? with
        | none =>
          by_cases h0 : args.length = 0
          · omega
          · have hlt : args.length - 1 < args.length := by omega
            rw [List.getElem?_eq_getElem hlt] at hlast
            cases hlast
        | some u =>
          obtain ⟨τ', hτ', _⟩ := hargs _ u hlast
          have := tyAt_arity _ _ _ hτ'
          omega
      rw [erase_apps]
      refine QReads.node hout hmin hV hres (A := bnd.ty)
        (by simp [varTy, Exit.occ, hbo, hlam]) hlen (by simp) ?_
      intro i a hi
      rw [List.getElem?_map] at hi
      cases hu : args[i]? with
      | none => simp [hu] at hi
      | some u =>
        simp only [hu, Option.map_some, Option.some.injEq] at hi
        subst hi
        obtain ⟨τi, hτi, hlsu⟩ := hargs i u hu
        obtain ⟨pre, post, hsplit, hlen'⟩ := getElem?_split args i u hu
        subst hsplit
        subst hlen'
        have happ : Term.apps (.var x π) (pre ++ u :: post)
            = Term.apps (.app (Term.apps (.var x π) pre) u) post := by
          simp [Term.apps]
        rw [happ] at hsub
        have hnode := (spine post _ c hsub).1
        have hfn : t.sub (.fn :: (List.replicate post.length .fn ++ c))
            = some (Term.apps (.var x π) pre) := by
          rw [sub_cons, hnode]
          rfl
        have harg : t.sub (.arg :: (List.replicate post.length .fn ++ c)) = some u := by
          rw [sub_cons, hnode]
          rfl
        have hbc : binder (List.replicate post.length .fn ++ c) x = .inr b := by
          rw [binder_replicate_fn]
          exact hbind
        have hE : List.replicate (pre ++ u :: post).length Dir.fn ++ c =
            List.replicate pre.length .fn ++ .fn :: (List.replicate post.length .fn ++ c) := by
          rw [List.length_append, List.length_cons]
          exact replicate_mid _ _ _ _
        have hτ : tyAt A₀ (childAddr (V.map Item.side) l pre.length) = some τi := by
          have e : childAddr (V.map Item.side) l pre.length
              = (V.map Item.side ++ List.replicate l .q ++ [.p]) ++
                (List.replicate pre.length .q ++ [.p]) := by
            simp [childAddr]
          rw [e, tyAt_append, htyb]
          exact hτi
        have hsides := childTape_sides V l
          ⟨List.replicate (pre ++ u :: post).length .fn ++ c, sv⟩ pre.length
        have hsv' : sv.length = argDepth (List.replicate post.length .fn ++ c) - argDepth b := by
          rw [argDepth_replicate_fn]
          exact hsv
        refine ih u (by simp) true (hide τi.order Γ) τi
          (.arg :: (List.replicate post.length .fn ++ c)) (⟨U.map Item.side, k⟩ :: anc)
          (childTape V l ⟨List.replicate (pre ++ u :: post).length .fn ++ c, sv⟩ pre.length) 0
          (.outside :: (sv ++ Lb)) hlsu harg ?_
          (fun k' hk => absurd hk (Nat.not_lt_zero _)) ?_ ?_ (fun h => by cases h) ?_
        · have h := qtop_arg pre hfn hbc hsv' htopb .outside
          rw [← hE] at h
          simpa [childTape] using h
        · rw [hsides]
          simp [childAddr, dropQ]
        · rw [hsides]
          simpa using hτ
        · intro x' bnd' hx' hz'
          rw [getElem?_hide] at hx'
          cases hx0 : Γ[x']? with
          | none => simp [hx0] at hx'
          | some bnd0 =>
            simp only [hx0, Option.map_some, Option.some.injEq] at hx'
            subst hx'
            obtain ⟨hkeep, hord⟩ := hideBind_visible hz'
            rw [hkeep] at hz' ⊢
            obtain ⟨b', V', l', sv', Lb', body', hbind', hlam', hL', hsv'', htop', hres', hV',
              hty', hglob'⟩ := hvars x' bnd0 hx0 hz'
            have hle := (binder_above hbind').1
            refine ⟨b', V', l', .outside :: sv', Lb', body', ?_, hlam', by simp [hL'], ?_,
              htop', resolve_enter ?_ hres', hV', hty', hglob'⟩
            · simp only [binder]
              rw [binder_replicate_fn]
              exact hbind'
            · simp only [List.length_cons, argDepth_arg, argDepth_replicate_fn, hsv'']
              omega
            · rw [hsides]
              intro heq
              cases hzone : bnd0.zone with
              | hid => exact hz' hzone
              | glob =>
                rw [hglob' hzone] at heq
                simp [childAddr] at heq
              | loc =>
                rw [List.append_assoc, tyAt_append] at hty'
                cases hσ : tyAt A₀ (V'.map Item.side) with
                | none => simp [hσ] at hty'
                | some σ =>
                  rw [hσ] at hty'
                  have h1 := tyAt_order l' σ bnd0.ty hty'
                  rw [← heq, hτ] at hσ
                  cases hσ
                  have h2 := hord hzone
                  omega

/-- A closed, locally safe normal form reads back as itself with the pointer machine. -/
theorem normal_qreads {t : Term} {A : Ty} (hsafe : LocallySafe t A) (hn : ∀ t', ¬ Step t t') :
    QReads t [] [] (erase t) :=
  qreads_nf (A₀ := A) (normal_of_nostep t hn) false [] A [] [] [] 0 [] hsafe rfl (qtop_root t)
    (fun _ hk => absurd hk (Nat.not_lt_zero _)) rfl (by simp [tyAt]) (fun _ => rfl)
    (fun x bnd hx => by simp at hx)

end LSL
