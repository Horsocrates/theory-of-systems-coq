(** * SheafLaplacianQ.v — НАПРАВЛЕНИЕ Н4 (ПЛАН-Иерархии-и-Каскады.md §9): the BRIDGE to cellular /
      network sheaves (Hansen-Ghrist), built over Q, with the inter-level Element/role-limit boundary IN
      the sheaf-Laplacian SPECTRUM.

   Cellular sheaf theory is the closest LIVE (non-ToS) field to "how adjacent systems influence
   neighbours across a hierarchy": data on a graph + restriction maps along edges + a Laplacian of
   consistency.  Almost all of it is over R.  The distinctive ToS angle: do it over Q, with the
   Element/role-limit boundary as the classifier of the Laplacian spectrum.

   We build the smallest genuine cellular sheaf over Q: a graph with 2 vertices u,v and 1 edge e, stalks
   F(u)=F(v)=F(e)=Q, restriction maps F_{u<e}=a, F_{v<e}=b (scalars in Q).  Then:

     -- coboundary  delta(xu,xv) = b*xv - a*xu  (the edge discrepancy);
     -- global sections H^0 = ker delta = consistent assignments (a*xu = b*xv); (b,a) is one;
     -- sheaf Laplacian  L = delta^* delta = [[a^2, -ab],[-ab, b^2]];  (Lx)_u = -a*delta(x),
        (Lx)_v = b*delta(x);
     -- HODGE: every global section is in ker L (and, for (a,b) =/= 0, ker L = ker delta);
     ★ -- the Laplacian SPECTRUM is on the Element side: disc(L) = (a^2-b^2)^2 + 4a^2b^2 = (a^2+b^2)^2 --
        a PERFECT SQUARE, so the modes {0, a^2+b^2} are rational (Element).  The 0-mode is H^0 (global
        sections), the a^2+b^2-mode is the inconsistency energy.

   THE BRIDGE (the genuine content, synthesis + construction level).  (1) Global sections H^0 = ker delta
   = the CONSISTENCY / conservation -- the sheaf analogue of the cascade conservation (a global section
   is a flux-free assignment, cf. ScaleHierarchyTransfer).  (2) The sheaf-Laplacian spectrum sits on the
   SAME Element/role-limit boundary as the rest of ToS (the HierarchyLaplacian disc-criterion).  (3) This
   ties ToS to the live field of network/cellular sheaves, in the distinctive over-Q + Element/role-limit
   register.

   HONEST SCOPE.  This is a SMALL sheaf (2 vertices, 1 edge) -- a genuine cellular-sheaf cohomology
   construction over Q (delta, H^0, L, Hodge, spectrum), 0 axioms, but minimal.  The Element side (the
   rank-1 sheaf Laplacian, rational spectrum) is fully genuine.  The role-limit side is shown as a SPECTRAL
   FOIL: a sheaf-Laplacian-shaped PSD rational matrix [[1,1],[1,2]] with disc 5 (surd, golden) -- realizing
   it by a cellular sheaf with rational coboundary is further work (cited disc-criterion: surd iff disc
   non-square).  The disc-criterion is reused from RealCouplingSpectrum (fresh .vo).  Level: synthesis +
   construction -- a bridge to a live field, modestly scoped.

   Elements: stalks Q at u,v,e; the restriction maps a,b in Q; the 2x2 sheaf Laplacian.
   Roles:    vertices/edge = cells; restriction maps = inter-cell maps; delta = inconsistency;
             global section = consistent (flux-free) assignment; the Laplacian modes.
   Rules:    delta(xu,xv)=b*xv-a*xu; H^0 = ker delta; L = delta^*delta; ker L >= H^0 (Hodge);
             disc(L) = (a^2+b^2)^2 (square) => Element spectrum.

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: клеточный пучок над Q (2 вершины, 1 ребро); stalks Q, restriction maps a,b.
     Rules (L5): кограница delta(xu,xv)=b*xv-a*xu; H^0=ker delta (согласованность); L=delta*delta;
                 ker L >= H^0 (Ходж); спектр L на границе Element/role-limit (disc-критерий).
     Roles (L4): вершины/ребро = ячейки; restriction maps = межуровневые отображения; delta = несогласов.;
                 глоб. сечение = flux-free назначение (= каскад-сохранение); собств. значения = моды.
     Elements  : stalks Q, a,b in Q; конечный граф; спектр {0, a^2+b^2} рацион.
     ОБРАЗУЮЩИЕ: Hansen-Ghrist (клеточные пучки); HierarchyLaplacian/RealCouplingSpectrum (disc-критерий);
                 ScaleHierarchyTransfer (сохранение = глоб. сечение).
     ВЛОЖЕННЫЕ : вершина = stalk-подсистема; H^0 = вложенное ядро (consistent); мода a^2+b^2 = вложенная
                 «энергия несогласованности».
   ДИАГНОСТИКА (P4): построена пучок-когомология над Q (delta, H^0, L, Ходж ker L>=H^0); глоб. сечения =
   каскад-сохранение (flux-free); спектр L на границе Element (disc=(a^2+b^2)^2 квадрат); role-limit foil
   [[1,1],[1,2]] disc 5 (golden). Мост к живому полю, отличие ToS = над Q + Element/role-limit. ЧЕСТНО:
   малый пучок; Element genuine, role-limit foil (реализация richer пучком = дальше).

   STATUS: 11 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.RealCouplingSpectrum.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Coboundary delta : C^0 = Q^2 -> C^1 = Q  (the edge discrepancy)        *)
(* ===================================================================== *)

(** Coboundary of the 2-vertex, 1-edge sheaf: delta(xu,xv) = b*xv - a*xu. *)
Definition delta (a b xu xv : Q) : Q := b * xv - a * xu.

(** ★ Global section (H^0 = ker delta): (xu,xv) = (b,a) is consistent (a*b = b*a). *)
Lemma global_section_ba : forall a b, delta a b b a == 0.
Proof. intros a b. unfold delta. ring. Qed.

(* ===================================================================== *)
(*  Sheaf Laplacian L = delta^* delta = [[a^2,-ab],[-ab,b^2]]              *)
(* ===================================================================== *)

Definition Lap_uu (a b : Q) : Q := a * a.
Definition Lap_uv (a b : Q) : Q := - (a * b).
Definition Lap_vu (a b : Q) : Q := - (a * b).
Definition Lap_vv (a b : Q) : Q := b * b.

Definition Lap_u (a b xu xv : Q) : Q := Lap_uu a b * xu + Lap_uv a b * xv.
Definition Lap_v (a b xu xv : Q) : Q := Lap_vu a b * xu + Lap_vv a b * xv.

(** ★ L = delta^* delta: (Lx)_u = -a*delta(x), (Lx)_v = b*delta(x). *)
Lemma Lap_is_delta_star_delta_u : forall a b xu xv,
  Lap_u a b xu xv == - a * delta a b xu xv.
Proof. intros. unfold Lap_u, Lap_uu, Lap_uv, delta. ring. Qed.

Lemma Lap_is_delta_star_delta_v : forall a b xu xv,
  Lap_v a b xu xv == b * delta a b xu xv.
Proof. intros. unfold Lap_v, Lap_vu, Lap_vv, delta. ring. Qed.

(* ===================================================================== *)
(*  Hodge: global sections live in ker L (and ker L = ker delta)           *)
(* ===================================================================== *)

(** ★ Every global section (ker delta) is in ker L -- the sheaf Hodge correspondence. *)
Lemma global_section_in_kerL : forall a b xu xv,
  delta a b xu xv == 0 -> Lap_u a b xu xv == 0 /\ Lap_v a b xu xv == 0.
Proof.
  intros a b xu xv H. split.
  - rewrite Lap_is_delta_star_delta_u, H. ring.
  - rewrite Lap_is_delta_star_delta_v, H. ring.
Qed.

(** Converse (for a =/= 0): ker L = ker delta -- harmonic = global section. *)
Lemma kerL_implies_kerDelta : forall a b xu xv,
  ~ (a == 0) -> Lap_u a b xu xv == 0 -> delta a b xu xv == 0.
Proof.
  intros a b xu xv Ha H.
  rewrite Lap_is_delta_star_delta_u in H.
  apply Qmult_integral in H. destruct H as [H|H].
  - exfalso. apply Ha. lra.
  - exact H.
Qed.

(* ===================================================================== *)
(*  ★ The sheaf-Laplacian spectrum on the Element/role-limit boundary       *)
(* ===================================================================== *)

(** ★ disc(L) = (a^2+b^2)^2 -- a perfect square: the sheaf-Laplacian spectrum is Element (rational). *)
Lemma sheaf_disc_square : forall a b,
  is_square_Q (cl_disc (Lap_uu a b) (Lap_uv a b) (Lap_vu a b) (Lap_vv a b)).
Proof.
  intros a b. exists (a*a + b*b).
  unfold cl_disc, Lap_uu, Lap_uv, Lap_vu, Lap_vv. ring.
Qed.

(** Hence a rational coupling mode exists (Element spectrum). *)
Lemma sheaf_spectrum_element : forall a b,
  exists lam, is_eigenvalue (Lap_uu a b) (Lap_uv a b) (Lap_vu a b) (Lap_vv a b) lam.
Proof.
  intros a b.
  apply (proj2 (spectrum_rational_iff_disc_square
                  (Lap_uu a b) (Lap_uv a b) (Lap_vu a b) (Lap_vv a b))).
  apply sheaf_disc_square.
Qed.

(** The 0-mode = global sections H^0 (det L = 0). *)
Lemma sheaf_eigenvalue_zero : forall a b,
  is_eigenvalue (Lap_uu a b) (Lap_uv a b) (Lap_vu a b) (Lap_vv a b) 0.
Proof.
  intros a b. unfold is_eigenvalue, cl_tr, cl_det, Lap_uu, Lap_uv, Lap_vu, Lap_vv. ring.
Qed.

(** The inconsistency-energy mode = a^2 + b^2 (the trace, since det = 0). *)
Lemma sheaf_eigenvalue_energy : forall a b,
  is_eigenvalue (Lap_uu a b) (Lap_uv a b) (Lap_vu a b) (Lap_vv a b) (a*a + b*b).
Proof.
  intros a b. unfold is_eigenvalue, cl_tr, cl_det, Lap_uu, Lap_uv, Lap_vu, Lap_vv. ring.
Qed.

(* ===================================================================== *)
(*  Role-limit foil: a sheaf-Laplacian-shaped matrix with surd spectrum     *)
(* ===================================================================== *)

(** ★ Role-limit foil: the PSD rational matrix [[1,1],[1,2]] has disc 5 (surd, golden) -- a sheaf whose
    spectrum is role-limit.  Realizing it by a cellular sheaf with rational coboundary is further work
    (disc-criterion: surd iff disc non-square, cited GoldenFibonacci/Sqrt5Irrational). *)
Example sheaf_role_limit_disc : cl_disc 1 1 1 2 == 5.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: cellular sheaf cohomology over Q on the Element/role-limit boundary *)
(* ===================================================================== *)

(** The over-Q cellular sheaf bridge:
      (global section) (b,a) is a global section H^0 = ker delta (a consistent, flux-free assignment);
      (★ Hodge)        every global section is in ker L (harmonic = consistent);
      (★ Element)      disc(L) = (a^2+b^2)^2 is a perfect square -- the sheaf-Laplacian spectrum is rational;
      (H^0 mode)       0 is an eigenvalue (the global-sections mode, det L = 0);
      (role-limit foil) [[1,1],[1,2]] has disc 5 (surd) -- a role-limit sheaf spectrum.
    Cellular sheaf cohomology built over Q (delta, H^0, sheaf Laplacian, Hodge), with global sections =
    the cascade conservation and the Laplacian spectrum on the SAME Element/role-limit boundary as the
    rest of ToS.  A bridge to the live field of network sheaves, in the over-Q + boundary register.
    Element side genuine; role-limit a spectral foil. *)
Theorem sheaf_laplacian_Q :
  (forall a b, delta a b b a == 0)
  /\ (forall a b xu xv, delta a b xu xv == 0 ->
        Lap_u a b xu xv == 0 /\ Lap_v a b xu xv == 0)
  /\ (forall a b, is_square_Q (cl_disc (Lap_uu a b) (Lap_uv a b) (Lap_vu a b) (Lap_vv a b)))
  /\ (forall a b, is_eigenvalue (Lap_uu a b) (Lap_uv a b) (Lap_vu a b) (Lap_vv a b) 0)
  /\ (cl_disc 1 1 1 2 == 5).
Proof.
  split; [exact global_section_ba |].
  split; [exact global_section_in_kerL |].
  split; [exact sheaf_disc_square |].
  split; [exact sheaf_eigenvalue_zero | exact sheaf_role_limit_disc].
Qed.
