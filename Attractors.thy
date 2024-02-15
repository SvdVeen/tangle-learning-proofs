theory Attractors
  imports Main ParityGames WinningRegions
begin

chapter \<open>Attractors\<close>
section \<open>Attractors for Arbitrary Players\<close>
(** We first define attractors in the context player_paritygame so we can prove properties for any
    player. *)
context player_paritygame begin
(** A maximal attractor for a target set. *)
inductive_set player_attractor :: "'v set \<Rightarrow> 'v set" for A where
  base: "x \<in> A \<Longrightarrow> x \<in> player_attractor A"
| player: "\<lbrakk> x \<in> V\<^sub>\<alpha>-A; (x,y)\<in>E; y\<in>player_attractor A \<rbrakk> \<Longrightarrow> x \<in> player_attractor A"
| opponent: "\<lbrakk> x \<in> V\<^sub>\<beta>-A; \<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>player_attractor A \<rbrakk> \<Longrightarrow> x \<in> player_attractor A"

(** The target set A is a subset of its maximal attractor. *)
lemma player_attractor_subset[simp]: "A \<subseteq> player_attractor A"
  by (auto intro: base)

(** Every node not part of the maximal attractor still has at least one successor. *)
lemma notin_player_attractor_succ:
  "\<lbrakk>v\<in>V; v \<notin> player_attractor A\<rbrakk> \<Longrightarrow> E `` {v} - player_attractor A \<noteq> {}"
  using player_attractor.simps succ V\<^sub>\<alpha>_subset by fast

(** A player's attractor is maximal; no player nodes have a successor in the attractor. *)
lemma player_attractor_max_player:
  "\<lbrakk>v\<in>V\<^sub>\<alpha>; v \<notin> player_attractor A\<rbrakk> \<Longrightarrow> \<forall>w \<in> E `` {v}. w \<notin> player_attractor A"
  using player_attractor.simps by fast

(** An opponent's attractor is maximal: no opponent nodes have a successor in the attractor. *)
lemma player_attractor_max_opponent:
  "\<lbrakk>v\<in>V\<^sub>\<beta>; v \<notin> player_attractor A\<rbrakk> \<Longrightarrow> \<exists>w \<in> E `` {v}. w \<notin> player_attractor A"
  using player_attractor.simps by fast


context
  fixes A :: "'v set"
begin
(** To prove important properties of attractors, we need to reason with ranks. *)
fun nodes_in_rank :: "nat \<Rightarrow> 'v set" where
  "nodes_in_rank 0 = A"
| "nodes_in_rank (Suc n) =
   nodes_in_rank n
   \<union> { x | x y. x\<in>V\<^sub>\<alpha> \<and> (x,y)\<in>E \<and> y\<in>nodes_in_rank n }
   \<union> { x. x\<in>V\<^sub>\<beta> \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>nodes_in_rank n) }"

(** nodes_in_rank is monotonous. *)
lemma nodes_in_rank_mono: "n\<le>m \<Longrightarrow> nodes_in_rank n \<subseteq> nodes_in_rank m"
  apply (induction m)
  by (auto simp: le_Suc_eq)

(** A is a subset of nodes_in_rank. *)
lemma nodes_in_rank_subset: "A \<subseteq> nodes_in_rank n"
  using nodes_in_rank.simps(1) nodes_in_rank_mono by blast

(** All edges in a rank n lead to a lower rank. *)
lemma nodes_in_rank_edges_lower:
  "\<lbrakk>x \<in> nodes_in_rank (Suc n); x \<notin> A; (x,y) \<in> E; x \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> y \<in> nodes_in_rank n"
  by (induction n) auto

(** All edges in a rank n lead to at most the same rank. *)
lemma nodes_in_rank_edges_same:
  "\<lbrakk>x \<in> nodes_in_rank n; x \<notin> A; (x, y) \<in> E; x \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> y \<in> nodes_in_rank n"
  by (induction n) auto

(** There exists a strategy for nodes_in_rank that forces all plays in the rank to go to A. *)
lemma nodes_in_rank_forces_A: "\<exists>\<sigma>.
  strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = (nodes_in_rank n - A) \<inter> V\<^sub>\<alpha> \<and> ran \<sigma> \<subseteq> nodes_in_rank n
  \<and> (\<forall>n'. n' \<le> n \<longrightarrow> (\<forall>x' \<in> nodes_in_rank n' - A. \<forall>y' \<in> (induced_subgraph \<sigma>) `` {x'}.
      y' \<in> nodes_in_rank n'))
  \<and> (\<forall>x\<in>nodes_in_rank n. \<forall>xs z. path (induced_subgraph \<sigma>) x xs z \<and> n<length xs \<longrightarrow> set xs \<inter> A \<noteq> {})"
proof (induction n)
  case 0 thus ?case
    apply (rule exI[where x=Map.empty])
    using origin_in_path by fastforce

next
  case (Suc n)
  from Suc.IH obtain \<sigma> where
    strat_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    dom_\<sigma>: "dom \<sigma> = (nodes_in_rank n-A) \<inter> V\<^sub>\<alpha>" and
    ran_\<sigma>: "ran \<sigma> \<subseteq> nodes_in_rank n" and
    closed_\<sigma>: "\<forall>n'. n'\<le>n \<longrightarrow> (\<forall>x' \<in> nodes_in_rank n'-A. \<forall>y' \<in> (induced_subgraph \<sigma>) `` {x'}.
      y' \<in> nodes_in_rank n')" and
    forces_\<sigma>: "\<forall>x\<in>nodes_in_rank n. \<forall>xs z. path (induced_subgraph \<sigma>) x xs z \<and> n<length xs
      \<longrightarrow> set xs \<inter> A \<noteq> {}"
    by blast
  let ?G\<sigma> = "induced_subgraph \<sigma>"

  define new_player_nodes where
    "new_player_nodes = (nodes_in_rank (Suc n) - nodes_in_rank n) \<inter> V\<^sub>\<alpha>"
  define target where
    "target \<equiv> \<lambda>x. SOME x'. x' \<in> nodes_in_rank n \<and> (x,x') \<in> E"

  have target_eq: "x \<in> new_player_nodes \<longleftrightarrow>
    (x \<in> nodes_in_rank (Suc n) \<and>
     x \<in> V\<^sub>\<alpha> \<and>
     x \<notin> nodes_in_rank n \<and>
     target x \<in> nodes_in_rank n \<and>
     (x,target x) \<in> E)" for x
    apply (rule iffI; simp add: new_player_nodes_def)
    using some_eq_imp[of _ "target x"]
    unfolding target_def by blast+

  define \<sigma>' where "\<sigma>' \<equiv> \<lambda>x. if x \<in> new_player_nodes then Some (target x) else \<sigma> x"
  let ?G\<sigma>' = "induced_subgraph \<sigma>'"

  show ?case
  proof (rule exI[where x=\<sigma>']; intro conjI allI ballI impI; (elim conjE)?)
    from strat_\<sigma> show \<sigma>'_strat: "strategy_of V\<^sub>\<alpha> \<sigma>'"
      unfolding \<sigma>'_def strategy_of_def E_of_strat_def
      by (safe; simp add: target_eq split: if_splits) blast+

    from dom_\<sigma> show \<sigma>'_dom: "dom \<sigma>' = (nodes_in_rank (Suc n)-A) \<inter> V\<^sub>\<alpha>"
      unfolding \<sigma>'_def new_player_nodes_def
      apply (safe; simp split: if_splits)
      using nodes_in_rank_subset by blast+

    from ran_\<sigma> show \<sigma>'_ran: "ran \<sigma>' \<subseteq> nodes_in_rank (Suc n)"
      unfolding \<sigma>'_def by (clarsimp simp: ran_def target_eq) blast

    {
      fix n' x' y'
      assume n'_leq_Suc_n: "n' \<le> Suc n"
         and x'_in_n'_min_A: "x' \<in> nodes_in_rank n'-A"
         and y'_succ_x': "y' \<in> ?G\<sigma>' `` {x'}"

      then consider (n'_leq_n) "n' \<le> n" | (n'_Suc_n) "n' = Suc n" by linarith
      thus "y' \<in> nodes_in_rank n'" proof cases
        case n'_leq_n
        from nodes_in_rank_mono[OF this] x'_in_n'_min_A
        have "x' \<notin> new_player_nodes"
          unfolding new_player_nodes_def by blast

        with y'_succ_x' have "(x',y') \<in> ?G\<sigma>"
          unfolding \<sigma>'_def induced_subgraph_def E_of_strat_def
          by auto

        with x'_in_n'_min_A n'_leq_n closed_\<sigma> show ?thesis by blast
      next
        case n'_Suc_n
        with x'_in_n'_min_A y'_succ_x' have
          x'_in_suc: "x' \<in> nodes_in_rank (Suc n)" and
          x'_notin_A: "x' \<notin> A" and
          edge: "(x',y') \<in> E " by auto
        with y'_succ_x' \<sigma>'_dom \<sigma>'_ran show ?thesis
          unfolding induced_subgraph_def E_of_strat_def
          apply (cases "x' \<in> V\<^sub>\<alpha>"; simp add: \<open>n'=Suc n\<close> target_eq ran_def)
          using nodes_in_rank_edges_same[OF x'_in_suc \<open>x'\<notin>A\<close> edge] by auto
      qed
    } note closed_\<sigma>'=this

    {
      fix x xs y
      assume x_in_n: "x\<in>nodes_in_rank n"
         and path: "path ?G\<sigma>' x xs y"
         and xs_no_A: "A \<inter> set xs = {}"

      have "path ?G\<sigma> x xs y"
      proof (cases xs)
        case Nil thus ?thesis using path by auto
      next
        case (Cons a list)
        with xs_no_A have "x \<notin> A"
          using origin_in_path[OF path] by blast
        with x_in_n have x_in_n_min_A: "x \<in> nodes_in_rank n - A" by blast

        have subgraph: "Restr ?G\<sigma>' (nodes_in_rank n) \<subseteq> ?G\<sigma>"
          unfolding \<sigma>'_def induced_subgraph_def E_of_strat_def
          by (auto simp: target_eq)

        from closed_\<sigma>'[of n] have
          "?G\<sigma>' `` (nodes_in_rank n-A) \<subseteq> nodes_in_rank n"
          by auto

        from path_partially_closed[OF x_in_n_min_A this path] xs_no_A have
          "set xs \<subseteq> nodes_in_rank n" "y \<in> nodes_in_rank n" by blast+
        from subgraph_path[OF subgraph path_restr_V[OF path this]]
        show ?thesis .
      qed
    } note xfer_lower_rank_path=this

    {
      fix x xs z
      assume x_in_suc: "x \<in> nodes_in_rank (Suc n)"
         and path: "path ?G\<sigma>' x xs z"
         and len: "Suc n < length xs"

      from x_in_suc consider
        (already_in) "x\<in>nodes_in_rank n"
      | (our_node) "x\<notin>nodes_in_rank n" "x\<in>V\<^sub>\<alpha>" "(x,target x)\<in>E" "target x\<in>nodes_in_rank n"
      | (opponent_node) "x\<notin>nodes_in_rank n" "x\<in>V\<^sub>\<beta>" "\<forall>y\<in>E``{x}. y\<in>nodes_in_rank n"
        using new_player_nodes_def target_eq by simp blast
      thus "set xs \<inter> A \<noteq> {}" proof cases
        case already_in with path len forces_\<sigma> show ?thesis
          using xfer_lower_rank_path Suc_lessD by fast

      next
        case our_node
        with x_in_suc have "(x,y)\<in>?G\<sigma>' \<Longrightarrow> y=target x" for y
          unfolding \<sigma>'_def induced_subgraph_def E_of_strat_def
          by (auto simp: target_eq split: if_splits)
        with path len obtain xs' where
          xs': "xs=x#xs'" "path ?G\<sigma>' (target x) xs' z"
          by (cases xs) auto

        show "set xs \<inter> A \<noteq> {}" proof
          assume xs_no_A: "set xs \<inter> A = {}"
          with xfer_lower_rank_path[OF \<open>target x \<in> nodes_in_rank n\<close>] xs'
          have "path ?G\<sigma> (target x) xs' z" by auto
          with xs_no_A len forces_\<sigma> \<open>target x \<in> nodes_in_rank n\<close> xs'
          show False by auto
        qed

      next
        case opponent_node
        with len path obtain xs' y where
          xs': "xs=x#xs'" "path ?G\<sigma>' y xs' z" "y\<in>nodes_in_rank n"
          by (cases xs) auto

        show "set xs \<inter> A \<noteq> {}" proof
          assume xs_no_A: "set xs \<inter> A = {}"
          with xfer_lower_rank_path xs'
          have "path ?G\<sigma> y xs' z" by auto
          with xs_no_A len forces_\<sigma> xs'
          show False by auto
        qed
      qed
    } note \<sigma>'_forces_A=this
  qed
qed (** End of proof nodes_in_rank_forces_A. *)
end (** End of context with fixed A. *)

(** nodes_in_rank is a subset of the maximal attractor. *)
lemma nodes_in_rank_ss_player_attractor: "nodes_in_rank A n \<subseteq> player_attractor A"
  apply (induction n)
  by (auto intro: player_attractor.intros)

(** There is a rank that contains all nodes in the maximal attractor. *)
lemma player_attractor_ss_nodes_in_rank:
  "x\<in>player_attractor A \<Longrightarrow> (\<exists>n. x\<in>nodes_in_rank A n)"
proof (induction rule: player_attractor.induct)
  case (base x) thus ?case using nodes_in_rank.simps(1) by fast
next
  case (player x y) thus ?case using nodes_in_rank.simps(2) by blast
next
  case (opponent x)
  define n_of_y where "n_of_y \<equiv> \<lambda>y. SOME n. y \<in> nodes_in_rank A n"
  have FIN: "finite (n_of_y ` E `` {x})" by auto
  have n_of_y: "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank A (n_of_y y)" for y
    unfolding n_of_y_def using opponent.IH by (auto intro: someI)

  define n_max where "n_max \<equiv> MAX y\<in>E``{x}. n_of_y y"
  have "(x,y)\<in>E \<Longrightarrow> (\<exists>i\<le>n_max. y\<in>nodes_in_rank A i)" for y
    using Max_ge[OF FIN] n_of_y unfolding n_max_def by blast
  hence y_in_n_max: "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank A n_max" for y
    using nodes_in_rank_mono[of _ _ A] by auto
  show ?case
    apply (rule exI[where x="Suc n_max"])
    using y_in_n_max opponent.hyps by simp
qed

(** The maximal attractor is the union of all ranks. *)
lemma player_attractor_eq_nodes_in_rank: "player_attractor A = \<Union>((nodes_in_rank A)`UNIV)"
  using player_attractor_ss_nodes_in_rank[of _ A] nodes_in_rank_ss_player_attractor[of A]
  by auto

(** nodes_in_rank is a subset of all of the target set in V. *)
lemma nodes_in_rank_ss: "nodes_in_rank A n \<subseteq> A \<union> V"
  apply (induction n)
  using V\<^sub>\<alpha>_subset by auto

(** If the target set is finite, so is nodes_in_rank. *)
lemma nodes_in_rank_finite[simp, intro!]: "finite A \<Longrightarrow> finite (nodes_in_rank A n)"
  using fin_V finite_Un[of A V] finite_subset[OF nodes_in_rank_ss, of A n] by simp

(** The maximal attractor is a subset of all of the target set in V. *)
lemma player_attractor_ss: "player_attractor A \<subseteq> A \<union> V"
  using player_attractor_ss_nodes_in_rank nodes_in_rank_ss by blast

lemma finite_union_nat_range_bound:
  fixes f :: "nat \<Rightarrow> 'a set"
  assumes FIN: "finite (\<Union>(range f))"
  assumes MONO: "\<And>n n'. n\<le>n' \<Longrightarrow> f n \<subseteq> f n'"
  shows "\<exists>n. \<Union>(range f) = f n"
proof -
  obtain n where "\<Union>(range f) = \<Union>{f i | i . i\<le>n}"
  proof -
    from finite_subset_image[OF finite_UnionD[OF FIN] order_refl]
    obtain C where 1: "finite C" "range f = f`C" by auto
    then obtain n where "C \<subseteq> {0..n}"
      by (meson atLeastAtMost_iff finite_nat_set_iff_bounded_le subset_eq zero_le)
    with 1 have "range f = f`{0..n}" by auto
    thus thesis by (force intro!: that[of n])
  qed
  also have "\<dots> = f n"
    using MONO
    by auto
  finally show ?thesis ..
qed

(** The attractor minus its target set is always finite. *)
lemma finite_player_attractor: "finite (player_attractor A - A)"
  using player_attractor_ss[of A] Diff_subset_conv[of "player_attractor A" A V]
    rev_finite_subset[OF fin_V]
  by simp

(** There exists a maximum rank that is equal to the maximal attractor. *)
lemma player_attractor_max_rank_eq: "\<exists>n. player_attractor A = nodes_in_rank A n"
proof -
  have 1: "\<Union>(range (nodes_in_rank A)) - A = \<Union>(range (\<lambda>x. nodes_in_rank A x - A))" by auto

  have "\<exists>n. player_attractor A - A = nodes_in_rank A n - A"
    using finite_player_attractor
    unfolding player_attractor_eq_nodes_in_rank
    apply (subst 1)
    apply (rule finite_union_nat_range_bound)
    apply simp
    by (simp add: Diff_mono nodes_in_rank_mono)

  thus ?thesis
    using player_attractor_subset[of A] nodes_in_rank_subset[of A] Diff_partition[of A "player_attractor A"]
    by blast
qed

(** There exists a strategy for the maximal attractor that forces all plays in it to go to A. *)
lemma player_attractor_attracts: "\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = (player_attractor A - A) \<inter> V\<^sub>\<alpha> \<and> ran \<sigma> \<subseteq> player_attractor A \<and>
  (\<forall>v\<in>player_attractor A - A. \<forall>v'. (v,v') \<in> (induced_subgraph \<sigma>) \<longrightarrow> v' \<in> player_attractor A) \<and>
  (\<forall>v\<in>player_attractor A. \<forall>xs. lasso' (induced_subgraph \<sigma>) v xs \<longrightarrow> set xs \<inter> A \<noteq> {})"
proof -
  obtain n where attr_x_rank_n: "player_attractor A = nodes_in_rank A n"
    using player_attractor_max_rank_eq by blast

  from nodes_in_rank_forces_A[of A n] obtain \<sigma> where
    strat_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    dom_\<sigma>: "dom \<sigma> = (nodes_in_rank A n - A) \<inter> V\<^sub>\<alpha>" and
    ran_\<sigma>: "ran \<sigma> \<subseteq> nodes_in_rank A n" and
    closed_\<sigma>: "(\<forall>n'. n' \<le> n \<longrightarrow> (\<forall>x'\<in>nodes_in_rank A n' - A. \<forall>y'\<in>induced_subgraph \<sigma> `` {x'}. y' \<in> nodes_in_rank A n'))" and
    forces_\<sigma>: "(\<forall>x\<in>nodes_in_rank A n. \<forall>xs z. path (induced_subgraph \<sigma>) x xs z \<and> n < length xs \<longrightarrow> set xs \<inter> A \<noteq> {})"
    by blast

  show ?thesis
  proof (rule exI[where x=\<sigma>]; intro conjI ballI impI allI)
    show "strategy_of V\<^sub>\<alpha> \<sigma>" by fact
    from dom_\<sigma> attr_x_rank_n show "dom \<sigma> = (player_attractor A - A) \<inter> V\<^sub>\<alpha>" by simp
    from ran_\<sigma> attr_x_rank_n show "ran \<sigma> \<subseteq> player_attractor A" by simp

    fix v v'
    assume v_in_attr_min_A: "v \<in> player_attractor A - A" and
           edge_in_subgame: "(v,v') \<in> induced_subgraph \<sigma>"
    with closed_\<sigma> show "v' \<in> player_attractor A"
      using attr_x_rank_n by fastforce

  next
    fix v xs
    assume v_in_attr: "v \<in> player_attractor A"
       and lasso_v_xs: "lasso' (induced_subgraph \<sigma>) v xs"

    from v_in_attr attr_x_rank_n have v_in_rank_n: "v \<in> nodes_in_rank A n" by simp

    from lasso'_extend_any_length[OF lasso_v_xs]
    obtain xs' where
      len_xs': "n < length xs'" and
      set_xs'_eq: "set xs = set xs'" and
      lasso_xs': "lasso' (induced_subgraph \<sigma>) v xs'"
      by blast

    from lasso'_impl_path[OF lasso_xs']
    obtain v' where "path (induced_subgraph \<sigma>) v xs' v'" by blast

    hence "set xs' \<inter> A \<noteq> {}" using forces_\<sigma> v_in_rank_n len_xs' by blast
    with set_xs'_eq show "set xs \<inter> A \<noteq> {}" by simp
  qed
qed

(** We can extend a winning region with an attractor. *)
lemma player_attractor_extends_winning_region:
  "player_winning_region W \<Longrightarrow> player_winning_region (player_attractor W)"
proof -
  let ?attr = "player_attractor W"

  assume winning_W: "player_winning_region W"
  hence "W \<subseteq> V" and W_closed_opp: "E `` (W \<inter> V\<^sub>\<beta>) \<subseteq> W"
    unfolding player_winning_region_def by auto
  from winning_W obtain \<sigma> where
    \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> W" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> W" and
    \<sigma>_winning: "\<forall>v\<in>W. \<forall>ys. reachable_cycle (induced_subgraph \<sigma>) v ys \<longrightarrow> winning_player ys"
    unfolding player_winning_region_def by auto
  let ?G\<sigma> = "induced_subgraph \<sigma>"
  from W_closed_opp \<sigma>_dom \<sigma>_ran
  have \<sigma>_closed: "?G\<sigma> `` W \<subseteq> W"
    using ind_subgraph_closed_region[OF \<open>W\<subseteq>V\<close>] by blast

  obtain \<sigma>' where
    \<sigma>'_strat: "strategy_of V\<^sub>\<alpha> \<sigma>'" and
    \<sigma>'_dom: "dom \<sigma>' = (?attr - W) \<inter> V\<^sub>\<alpha>" and
    \<sigma>'_ran: "ran \<sigma>' \<subseteq> ?attr" and
    \<sigma>'_closed: "\<forall>v\<in>?attr - W. \<forall>v'. (v,v') \<in> induced_subgraph \<sigma>' \<longrightarrow> v'\<in>?attr" and
    \<sigma>'_forces_W: "\<forall>v\<in>?attr. \<forall>xs. lasso' (induced_subgraph \<sigma>') v xs \<longrightarrow> set xs \<inter> W \<noteq> {}"
    using player_attractor_attracts[of W] by auto
  let ?G\<sigma>' = "induced_subgraph \<sigma>'"
  from \<sigma>'_closed have \<sigma>'_closed': "?G\<sigma>' `` (?attr - W) \<subseteq> ?attr"
    by blast

  define \<tau> where "\<tau> = \<sigma> ++ \<sigma>'"
  let ?G\<tau> = "induced_subgraph \<tau>"
  from \<sigma>_dom \<sigma>'_dom have doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}" by auto
  from \<sigma>'_forces_W have \<tau>_forces_W:
    "\<forall>v\<in>?attr. \<forall>xs. lasso' ?G\<tau> v xs \<longrightarrow> set xs \<inter> W \<noteq> {}"
    unfolding \<tau>_def using ind_subgraph_add_disjoint(2)[OF doms_disj]
    by (simp add: subgraph_lasso')
  from \<sigma>_closed have \<tau>_closed_W: "?G\<tau> `` W \<subseteq> W"
    unfolding \<tau>_def using ind_subgraph_add_disjoint(1)[OF doms_disj]
    by blast

  from \<open>W \<subseteq> V\<close> have attr_in_V: "?attr \<subseteq> V"
    using player_attractor_ss[of W] by blast

  moreover from \<sigma>_strat \<sigma>'_strat have \<tau>_strat: "strategy_of V\<^sub>\<alpha> \<tau>"
    unfolding \<tau>_def by auto

  moreover from \<sigma>_dom \<sigma>'_dom have \<tau>_dom: "dom \<tau> = V\<^sub>\<alpha> \<inter> ?attr"
    unfolding \<tau>_def by (auto simp: player_attractor.base)

  moreover from doms_disj \<sigma>_ran \<sigma>'_ran have \<tau>_ran: "ran \<tau> \<subseteq> ?attr"
    unfolding \<tau>_def using ran_map_add[of \<sigma> \<sigma>']
    by (auto simp: player_attractor.base)

  moreover from \<sigma>_closed \<sigma>'_closed' have \<tau>_closed:
    "?G\<tau> `` ?attr \<subseteq> ?attr"
    unfolding \<tau>_def
    using ind_subgraph_add_disjoint[OF doms_disj] player_attractor_subset[of W]
    by blast
  with \<tau>_dom have attr_closed_opp: "E `` (?attr \<inter> V\<^sub>\<beta>) \<subseteq> ?attr"
    using ind_subgraph_notin_dom[of _ _ \<tau>] by fast

  moreover have \<tau>_winning:
    "\<forall>v\<in>?attr. \<forall>ys. reachable_cycle ?G\<tau> v ys \<longrightarrow> winning_player ys"
  proof (rule ballI; rule allI; rule impI)
    fix v ys
    assume v_in_attr: "v \<in> ?attr" and reachable_cycle: "reachable_cycle ?G\<tau> v ys"
    hence ys_notempty: "ys \<noteq> []" by auto
    from reachable_cycle_closed_set[OF v_in_attr \<tau>_closed reachable_cycle]
    have ys_in_attr: "set ys \<subseteq> ?attr" .

    with reachable_cycle obtain y where
      cycle: "cycle ?G\<tau> y ys" and
      y_in_attr: "y \<in> ?attr"
      unfolding reachable_cycle_def
      using origin_in_cycle by fast

    with \<tau>_forces_W have W_in_ys: "set ys \<inter> W \<noteq> {}"
      using cycle_impl_lasso' by fast

    from cycle_intersects_closed_region[OF cycle this \<tau>_closed_W]
    have ys_in_W: "set ys \<subseteq> W" and y_in_W: "y \<in> W"
      using origin_in_cycle[OF cycle] by auto

    have subset: "Restr ?G\<tau> W \<subseteq> ?G\<sigma>"
      unfolding \<tau>_def
      using ind_subgraph_add_disjoint(1)[OF doms_disj] by blast
    from subgraph_cycle[OF subset cycle_restr_V[OF cycle ys_in_W]]
    have "reachable_cycle ?G\<sigma> y ys"
      using cycle_impl_reachable_cycle by fast

    with \<sigma>_winning y_in_W show "winning_player ys" by blast
  qed

  ultimately show ?thesis
    unfolding player_winning_region_def by blast
qed

end (** End of context player_paritygame. *)


(** We put our definitions for players' attractors in player_paritygame into the context of the
    general paritygame with specified players. *)
section \<open>Attractors for Specific Players\<close>
context paritygame begin

(** An attractor for a specific player. *)
fun attractor where
  "attractor EVEN = P0.player_attractor"
| "attractor ODD = P1.player_attractor"

(** The target set A is a subset of an attractor. *)
lemma attractor_subset: "A \<subseteq> attractor \<alpha> A"
  using P0.player_attractor_subset P1.player_attractor_subset by (cases \<alpha>) auto

(** If the target set is part of the graph, so is the attractor. *)
lemma attractor_subset_graph: "A \<subseteq> V \<Longrightarrow> attractor \<alpha> A \<subseteq> V"
  using P0.player_attractor_ss P1.player_attractor_ss by (cases \<alpha>; simp) blast+

(** If a node is not in the attractor, then they have a successor in the graph with the attractor
    removed from it. *)
lemma notin_attractor_succ: "\<lbrakk>v \<in> V ; v \<notin> attractor \<alpha> A\<rbrakk> \<Longrightarrow> E `` {v} - attractor \<alpha> A \<noteq> {}"
  using P0.notin_player_attractor_succ P1.notin_player_attractor_succ by (cases \<alpha>) auto

(** The attractor is maximal for the player; all player nodes not in the attractor have no successors
    in it. *)
lemma attractor_max_player:
  "\<lbrakk>v \<in> V_player \<alpha>; v \<notin> attractor \<alpha> A\<rbrakk> \<Longrightarrow> \<forall>w \<in> E `` {v}. w \<notin> attractor \<alpha> A"
  using P0.player_attractor_max_player P1.player_attractor_max_player
  by (cases \<alpha>) auto

(** The attractor is maximal for the opponent: all opponent nodes not in the attractor have at least
    one successor that is also not in the attractor. *)
lemma attractor_max_opponent:
  "\<lbrakk>v \<in> V_opponent \<alpha>; v \<notin> attractor \<alpha> A\<rbrakk> \<Longrightarrow> \<exists>w \<in> E `` {v}. w \<notin> attractor \<alpha> A"
  using P0.player_attractor_max_opponent
  using P1.player_attractor_max_opponent
  using V\<^sub>0_in_V by (cases \<alpha>) auto

(** The player has a strategy that forces all plays in the attractor to move to the target. *)
lemma attractor_attracts: "\<exists>\<sigma>. strategy_of (V_player \<alpha>) \<sigma> \<and>
    dom \<sigma> = (attractor \<alpha> A - A) \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> attractor \<alpha> A \<and>
    (\<forall>v\<in>attractor \<alpha> A - A. \<forall>v'. (v,v') \<in> induced_subgraph \<sigma> \<longrightarrow> v' \<in> attractor \<alpha> A) \<and>
    (\<forall>v\<in>attractor \<alpha> A. \<forall>xs. lasso' (induced_subgraph \<sigma>) v xs \<longrightarrow> set xs \<inter> A \<noteq> {})"
  using P0.player_attractor_attracts P1.player_attractor_attracts by (cases \<alpha>) auto

(** We can extend a winning region with an attractor. *)
lemma attractor_extends_winning_region:
  "winning_region \<alpha> W \<Longrightarrow> winning_region \<alpha> (attractor \<alpha> W)"
  using P0.player_attractor_extends_winning_region
  using P1.player_attractor_extends_winning_region
  by (cases \<alpha>; simp)

lemma remove_attractor_subgame[simp]:
  "valid_subgame (V-attractor \<alpha> A)"
  apply simp
  apply (unfold_locales; clarsimp)
  using notin_attractor_succ E_in_V by blast


end (** End of context paritygame. *)

end
