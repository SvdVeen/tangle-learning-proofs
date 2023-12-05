theory TangleLearning_Search
imports Main TangleAttractors TangleLearning
begin

context paritygame begin

(** I may want to use this and move it to paritygames.thy.
    More, similar abbreviations for using concepts in a restricted subgame may be useful for
    legibility.*)
abbreviation (input) valid_subgame :: "'v set \<Rightarrow> bool" where
  "valid_subgame R \<equiv> R \<subseteq> V \<and> paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"

abbreviation (input) bound_nt_bottom_SCC :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v set \<Rightarrow> bool" where
  "bound_nt_bottom_SCC Z \<sigma> S \<equiv> S \<subseteq> Z \<and>
    finite_graph_V.nt_bottom_SCC (induced_subgraph (dom \<sigma>) \<sigma>) (induced_subgraph_V (dom \<sigma>) \<sigma>) S"

abbreviation (input) subgraph_tattr
  :: "'v set \<Rightarrow> player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "subgraph_tattr R \<alpha> T A Z \<sigma> \<equiv> paritygame.tangle_attractor (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> T A Z \<sigma>"

context
  fixes T :: "'v set set"
  assumes tangles_T: "\<forall>t\<in>T. tangle EVEN t \<or> tangle ODD t"
  assumes open_tangles_T: "\<forall>t\<in>T. tangle \<alpha> t \<longrightarrow> E `` (t \<inter> V_opponent \<alpha>) - U \<noteq> {}"
  assumes fin_T: "finite T"
begin

(** search_step represents a single iteration of the while-loop in the search algorithm. *)
inductive search_step :: "'v set \<times> 'v set set \<Rightarrow> 'v set \<times> 'v set set \<Rightarrow> bool" where
  step:
  "\<lbrakk>R \<noteq> {};
    p = pr_set R; \<alpha> = player_wins_pr p;
    A = {v. v \<in> R \<and> pr v = p};
    subgraph_tattr R \<alpha> T A Z \<sigma>;
    Ov = {v \<in> V_player \<alpha> \<inter> A. E `` {v} \<inter> Z \<noteq> {}} \<union> {v \<in> V_opponent \<alpha> \<inter> A. (E `` {v}) \<inter> R \<subseteq> Z};
    Y' = (if Ov \<noteq> {} then Y \<union> {S. bound_nt_bottom_SCC Z \<sigma> S} else Y);
    R' = R-Z\<rbrakk> \<Longrightarrow> search_step (R,Y) (R',Y')"

lemmas search_step_induct[consumes 1, case_names step] =
  search_step.induct[
    of "(R,Y)" "(R',Y')" for R Y R' Y',
    where P="\<lambda>(a,b) (c,d). P a b c d" for P,
    unfolded split]

(** If the initial R is finite, then R' is finite after a step. *)
lemma search_step_R_finite:
  "\<lbrakk>search_step (R,Y) (R',Y'); finite R\<rbrakk> \<Longrightarrow> finite R'"
  apply (induction rule: search_step_induct) by blast

(** If the initial R is a valid subgame, then R' is a valid subgame after a step. *)
lemma search_step_valid_subgame:
  "\<lbrakk>search_step (R,Y) (R',Y'); valid_subgame R\<rbrakk> \<Longrightarrow> valid_subgame R'"
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence tattr: "subgraph_tattr R \<alpha> T A Z \<sigma>" and
    R_valid_game: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
    by blast+

  from \<open>R' = R-Z\<close> \<open>valid_subgame R\<close> have "R' \<subseteq> V" by auto

  moreover from \<open>R' \<subseteq> V\<close> \<open>R' = R-Z\<close> have "paritygame (Restr E R') (V\<inter>R') (V\<^sub>0\<inter>R')"
    using paritygame.remove_tangle_attractor_subgame[OF R_valid_game fin_T tattr]
    by (simp add: Times_Int_Times Int_assoc Int_absorb1 Int_Diff)

  ultimately show ?case ..
qed

(*
(** search_step is inversely monotonous on R: R strictly decreases with every step. *)
lemma search_step_R_anti_mono: "search_step S S' \<Longrightarrow> fst S' \<subset> fst S"
proof (induction rule: search_step.induct)
  case (step R p \<alpha> A T\<^sub>\<alpha> Z \<sigma> V\<^sub>\<alpha> V\<^sub>\<beta> Ov Y' Y R')
  (** We know that every t in T\<^sub>\<alpha> is a tangle in the subgame of R, and that T\<^sub>\<alpha> is finite. We need
      these properties for showing the next two properties. *)
  from step(7) have tangles_T\<^sub>\<alpha>: "\<forall>t\<in>T\<^sub>\<alpha>. paritygame.tangle (Restr E R) (V \<inter> R) (V\<^sub>0 \<inter> R) pr \<alpha> t"
    by blast
  from step(7) have fin_T\<^sub>\<alpha>: "finite T\<^sub>\<alpha>"
    using finite_subset[OF _ fin_T] by simp
  (** We show that Z is not empty. *)
  have "Z \<noteq> {}" proof -
    (** R is finite *)
    from finite_subset[OF step(2) fin_V] have fin_R: "finite R" .
    (** A is part of the finite non-empty set R, therefore, it must contain at least one node
        with priority p, and thus it is not empty. *)
    from step(6) step(4) have "A \<noteq> {}"
      using pr_set_exists[OF fin_R step(1)] by blast
    (** Since the target A is part of the tangle-attracted region Z, Z must also be non-empty. *)
    with paritygame.target_in_tangle_attractor[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)]
    show ?thesis by auto
  qed
  (** Furthermore, Z is a subset of of R. *)
  moreover have "Z \<subseteq> R" proof -
    from step(6) have A_in_R: "A \<subseteq> R" by simp
    (** Since the tangle-attracted Z region is a subset of the graph restricted to R  and the target
        set A, we can show that it is a subset R. *)
    with paritygame.tangle_attractor_ss[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)] step(2)
    show ?thesis by blast
  qed
  (** Since R' is obtained by removing Z from R, and we know that Z is a non-empty a subset of R,
      R decreases monotonically with every step. *)
  ultimately show ?case using step(13) by auto
qed

(** Because R is finite and decreases with every step, search_step is a well-founded relation. *)
lemma search_step_wellfounded: "wfP (search_step\<inverse>\<inverse>)"
  unfolding wfP_def
  apply (rule wf_subset[of "inv_image (finite_psubset) (\<lambda>(R,Y). R)"]; clarsimp)
  subgoal for R' Y' R Y
    using search_step_R_anti_mono[of "(R,Y)" "(R',Y')"] search_step_R_finite[of "(R,Y)"]
    by simp
  done

(** If R is a valid non-empty subgame, then search_step can always be applied.
    The specifics of Y are not relevant, as it has no preconditions in the step. *)
lemma search_step_continues_on_valid_R:
  "\<lbrakk>R \<noteq> {}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)\<rbrakk> \<Longrightarrow> Domainp search_step (R,Y)"
proof -
  assume R_notempty: "R\<noteq>{}" and
         R_in_V: "R \<subseteq> V" and
         R_valid_subgame: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  (** All we have to do is define the local variables with their conditions in the step. *)
  moreover define p where "p = pr_set R"
  moreover define \<alpha> where "\<alpha> = player_wins_pr p"
  moreover define A where "A = {v. v\<in>R \<and> pr v = p}"
  moreover define T\<^sub>\<alpha> where "T\<^sub>\<alpha> = {t. t \<in> T \<and> paritygame.tangle (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> t}"
  moreover from T\<^sub>\<alpha>_def have
    tangles_T\<^sub>\<alpha>: "\<forall>t\<in>T\<^sub>\<alpha>. paritygame.tangle (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> t" and
    fin_T\<^sub>\<alpha>: "finite T\<^sub>\<alpha>"
    using finite_subset[OF _ fin_T] by auto
  moreover obtain Z \<sigma> where
    "paritygame.tangle_attractor (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> T\<^sub>\<alpha> A Z \<sigma>"
    using paritygame.tangle_attractor_exists[OF R_valid_subgame tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha>] by blast
  moreover define V\<^sub>\<alpha> where "V\<^sub>\<alpha> = V_player \<alpha>"
  moreover define V\<^sub>\<beta> where "V\<^sub>\<beta> = V_opponent \<alpha>"
  moreover define Ov where
    "Ov = {v. v \<in> V\<^sub>\<alpha>\<inter>A \<and> E `` {v} \<inter> Z \<noteq> {}} \<union> {v. v \<in> V\<^sub>\<beta>\<inter>A \<and> (E `` {v}) \<inter> R \<subseteq> Z}"
  moreover define Y' where "Y' = (if Ov \<noteq> {} then
      Y \<union> {S. S \<subseteq> Z \<and> finite_graph_V_Succ.nt_bottom_SCC (induced_subgraph V\<^sub>\<alpha> \<sigma>) (induced_subgraph_V V\<^sub>\<alpha> \<sigma>) S}
   else
      Y)"
  moreover define R' where "R' = R-Z"
  (** Now, we can put them in their place in the step, and our thesis follows automatically. *)
  ultimately have "search_step (R,Y) (R',Y')"
    using search_step.step by blast
  thus ?thesis by blast
qed

(** If we start from a valid, non-empty subgame, through applying search_step, we will always reach
    a final state with a corresponding Y. *)
lemma search_step_terminates_with_Y:
  "\<lbrakk>fst S \<noteq> {}; fst S \<subseteq> V; paritygame (Restr E (fst S)) (V\<inter>fst S) (V\<^sub>0\<inter>fst S)\<rbrakk>
  \<Longrightarrow> \<exists>Y. search_step\<^sup>*\<^sup>* S ({},Y)"
  using search_step_wellfounded
  unfolding wfP_def
proof (induction S rule: wf_induct_rule)
  case (less x)
  (** Because R in x is a valid non-empty subgame, we know there is a state y that succeeds
      it in search_step. *)
  from search_step_continues_on_valid_R[OF less.prems, of "snd x"]
  have "Domainp search_step x" by simp
  then obtain y where step_x_y: "search_step x y" by blast
  (** Now we consider whether R' in the successor y is empty or not. *)
  consider (empty_R') "fst y = {}" | (nonempty_R') "fst y \<noteq> {}" by blast
  thus ?case proof cases
    (** If R' in y is already empty, we clearly have a step from x to an endpoint. *)
    case empty_R'
    with step_x_y have "search_step x ({}, snd y)"
      using surjective_pairing[of y] by auto
    thus ?thesis by blast
  next
    (** If R' is not empty, then we know it is a valid subgame in V by the properties of the
        step. *)
    case nonempty_R'
    moreover from search_step_R_in_V[OF step_x_y] have "fst y \<subseteq> V" ..
    moreover from step_result_R_is_paritygame[OF step_x_y]
    have "paritygame (Restr E (fst y)) (V \<inter> fst y) (V\<^sub>0 \<inter> fst y)" .
    moreover note step_x_y
    (** By the induction hypothesis, we then know that from y, we can reach a state with an empty
        R and a valid Y.*)
    ultimately obtain Y where "search_step\<^sup>*\<^sup>* y ({}, Y)"
      using less.IH by blast
    (** We also know you can reach y from x. By the transitivity of the reflexive transitive
        closure, we can now say that we can reach the state with an empty R from x, via y. *)
    moreover from step_x_y have "search_step\<^sup>*\<^sup>* x y" by simp
    ultimately show ?thesis using rtranclp_trans by fast
  qed
qed

(** When an empty R is reached, there exist no further steps in the algorithm. *)
lemma search_terminates_on_empty_R: "\<not>Domainp search_step ({},Y)"
  using search_step_R_anti_mono[of "({},Y)"]
  by auto
*)

(** TODO: invariant, prove property of Y on termination. *)
(** The current invariant states that everything contained in Y is a tangle.
    This should probably be restated to say that everything contained in Y is a tangle with its
    corresponding strategy. *)
(**
definition search_I ::  "'v set \<times> 'v set set \<Rightarrow> bool" where
  "search_I S \<equiv> finite (snd S) \<and> (\<forall>U \<in> snd S. \<exists>\<alpha>. tangle \<alpha> U) \<and> (fst S={} \<longrightarrow> \<dots>)"
*)

definition search_I :: "'v set \<times> 'v set set \<Rightarrow> bool" where
  "search_I \<equiv> \<lambda>(R,Y). finite R \<and> valid_subgame R \<and> finite Y \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T)"

(** If we end with an empty region, then we have a finite, non-empty Y containing new tangles that
    were not included in T before, as specified by our invariant. *)
lemma search_I_correct:
  "search_I ({},Y) \<Longrightarrow> finite Y \<and> Y \<noteq> {} \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T)"
  unfolding search_I_def apply simp sorry

(** If our invariant holds for a state, a step of the search algorithm gives us a finite Y'. *)
lemma search_step_finite_Y:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> finite Y'"
  apply (induction rule: search_step_induct)
  using paritygame.tangle_attractor_finite[OF _ fin_T]
  unfolding search_I_def by force

(** If our invariant holds for a state, a step of the search algorithm gives us a Y' with new tangles
    that were not included in T before. *)
lemma search_step_tangles_Y:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> \<forall>U \<in> Y'. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T"
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence attr: "subgraph_tattr R \<alpha> T A Z \<sigma>" and
    A_def: "A = {v \<in> R. pr v = p}" and
    Ov_def: "Ov = {v \<in> V_player \<alpha> \<inter> A. E `` {v} \<inter> Z \<noteq> {}}
      \<union> {v \<in> V_opponent \<alpha> \<inter> A. E `` {v} \<inter> R \<subseteq> Z}" and
    Y'_def: "Y' = (if Ov \<noteq> {} then Y \<union> {S. bound_nt_bottom_SCC Z \<sigma> S} else Y)" and
    new_tangles_Y: "\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T" and
    R_in_V: "R \<subseteq> V" and
    R_valid_game: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
    unfolding search_I_def by auto

  from A_def paritygame.target_in_tangle_attractor[OF R_valid_game fin_T attr]
    paritygame.tangle_attractor_ss[OF R_valid_game fin_T attr]
  have A_in_Z: "A \<subseteq> Z" and Z_in_R: "Z \<subseteq> R" by blast+
  with R_in_V paritygame.player_strat_in_E[OF R_valid_game]
    paritygame.tangle_attractor_strat[OF R_valid_game fin_T attr] have
    \<sigma>_strat: "strategy_of (V_player \<alpha> \<inter> Z) \<sigma>" and
    \<sigma>_dom: "dom \<sigma> \<subseteq> V_player \<alpha> \<inter> Z" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> Z" and
    \<sigma>_partially_closed: "(Restr (induced_subgraph (V_player \<alpha>) \<sigma>) R) `` (Z-A) \<subseteq> Z" and
    \<sigma>_forces_A_or_wins:
      "(\<forall>x\<in>Z. \<forall>xs ys. lasso_from_node (Restr (induced_subgraph (V_player \<alpha>) \<sigma>) R) x xs ys
        \<longrightarrow>set (xs @ ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys)"
    unfolding restr_subgraph_V_player[OF R_valid_game]
      restr_ind_subgraph_V\<^sub>\<alpha>[OF paritygame.axioms[OF R_valid_game]]
    unfolding strategy_of_player_def strategy_of_def by auto

  have all_games_in_Z_won:
    "\<forall>v\<in>Z. \<forall>xs ys. lasso_from_node (Restr (induced_subgraph (V_player \<alpha>) \<sigma>) Z) v xs ys
      \<longrightarrow> player_wins_list \<alpha> ys"
  proof -
    from R_in_V step(2,3) have "player_winningP \<alpha> (pr_set (V \<inter> R))"
      by (cases \<alpha>; simp add: player_wins_pr_def Int_absorb1 split: if_splits)
    moreover from R_in_V step(2,4) have "A = {v \<in> V \<inter> R. pr v = pr_set (V \<inter> R)}"
      by (simp add: Int_absorb1)
    ultimately show ?thesis
      using paritygame.van_dijk_2[OF R_valid_game fin_T _ _ attr]
      unfolding restr_subgraph_V_player[OF R_valid_game]
        restr_ind_subgraph_V\<^sub>\<alpha>[OF paritygame.axioms[OF R_valid_game]]
        Restr_subset[OF Z_in_R] by simp
  qed

  show ?case
  proof (rule ballI)
    fix U assume Y_in_Y': "U \<in> Y'"
    with Y'_def consider (old) "U \<in> Y" | (new) "U \<in> {S. bound_nt_bottom_SCC Z \<sigma> S}"
      by (auto split: if_splits)
    thus "\<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T" proof cases
      case old with new_tangles_Y show ?thesis by blast
    next
      case new
      from new have U_in_Z: "U \<subseteq> Z" by blast
      with R_in_V Z_in_R have U_in_V: "U \<subseteq> V" by blast
      from finite_subset[OF this fin_V] have fin_U: "finite U" .
      from new have U_notempty: "U \<noteq> {}"
        using finite_graph_V.nt_bottom_SCC_notempty by force

      let ?\<sigma>_graph = "induced_subgraph (dom \<sigma>) \<sigma>"
      let ?\<sigma>_graph_V = "induced_subgraph_V (dom \<sigma>) \<sigma>"
      have fin_graph_\<sigma>: "finite_graph_V ?\<sigma>_graph ?\<sigma>_graph_V" by simp

      from new have \<sigma>_connected: "strongly_connected (Restr ?\<sigma>_graph U) (?\<sigma>_graph_V \<inter> U)"
        using finite_graph_V.nt_bottom_SCC_strongly_connected[OF fin_graph_\<sigma>] by blast
      from new have \<sigma>_U_succ_in_U: "\<forall>v\<in>U. \<exists>v'\<in>U. (v,v') \<in> ?\<sigma>_graph"
        using finite_graph_V.nt_bottom_SCC_succ_in_SCC[OF fin_graph_\<sigma>] by blast

      define \<sigma>' where "\<sigma>' = \<sigma> |` U"
      let ?\<sigma>'_graph = "induced_subgraph (dom \<sigma>') \<sigma>'"
      let ?\<sigma>'_graph_V = "induced_subgraph_V (dom \<sigma>') \<sigma>'"
      have \<sigma>'_le_\<sigma>: "\<sigma>' \<subseteq>\<^sub>m \<sigma>" by (auto simp: \<sigma>'_def map_le_def)

      from restricted_strat_subgraph_same_in_region[OF \<sigma>'_def] have graphs_equal_in_U:
        "Restr ?\<sigma>_graph U = Restr ?\<sigma>'_graph U" .
      from restricted_strat_subgraph_V_same_in_region[OF \<sigma>'_def] new have graph_V_equal_in_U:
        "?\<sigma>_graph_V \<inter> U = ?\<sigma>'_graph_V \<inter> U"
        using finite_graph_V.nt_bottom_SCC_in_V[OF fin_graph_\<sigma>] by blast

      from \<sigma>_U_succ_in_U graphs_equal_in_U have \<sigma>'_U_succ_in_U:
        "\<forall>v\<in>U. \<exists>v'\<in>U. (v, v') \<in> induced_subgraph (dom \<sigma>') \<sigma>'" by blast

      from \<sigma>_strat have \<sigma>'_strat: "strategy_of (V_player \<alpha>) \<sigma>'"
        using strat_le_E_of_strat[OF \<sigma>'_le_\<sigma>]
        unfolding strategy_of_def \<sigma>'_def by auto

      have \<sigma>'_dom: "dom \<sigma>' = U \<inter> V_player \<alpha>"
      proof
        from \<sigma>_dom show "dom \<sigma>' \<subseteq> U \<inter> V_player \<alpha>" unfolding \<sigma>'_def by auto
      next
        {
          fix x assume assm: "x \<in> V_player \<alpha> \<inter> A \<inter> U"
          with U_in_Z Z_in_R \<sigma>'_U_succ_in_U
          have "Restr E R `` {x} \<inter> U \<noteq> {}"
            using ind_subgraph by fast
          with assm U_in_Z have "x \<in> dom \<sigma>'"
            using paritygame.tangle_attractor_strat_in_dom_A[OF R_valid_game fin_T attr, of x]
            unfolding restr_subgraph_V_player[OF R_valid_game] \<sigma>'_def by auto
        }
        moreover
        {
          fix x assume "x \<in> V_player \<alpha> \<inter> (U-A)"
          with Z_in_R U_in_Z have "x \<in> dom \<sigma>'"
            using paritygame.tangle_attractor_strat_in_dom_not_A[OF R_valid_game fin_T attr, of x]
            unfolding restr_subgraph_V_player[OF R_valid_game] \<sigma>'_def by fastforce
        }
        ultimately show "U \<inter> V_player \<alpha> \<subseteq> dom \<sigma>'" by blast
      qed

      from \<sigma>'_U_succ_in_U have \<sigma>'_ran: "ran \<sigma>' \<subseteq> U"
        unfolding \<sigma>'_def
        using ran_restrictD[of _ \<sigma> U] ind_subgraph_to_strategy by fastforce

      have "EV (Restr ?\<sigma>'_graph U) \<subseteq> EV ?\<sigma>'_graph \<inter> U" by auto
      hence \<sigma>'_connected:
        "strongly_connected (tangle_subgraph \<alpha> U \<sigma>') (EV (tangle_subgraph \<alpha> U \<sigma>'))"
        unfolding tangle_subgraph_is_restricted_ind_subgraph[OF U_in_V \<sigma>'_dom \<sigma>'_ran]
          strongly_connected_def
        apply (intro conjI)
        subgoal using U_notempty \<sigma>'_U_succ_in_U by blast
        subgoal by (auto intro: rev_image_eqI)
        subgoal using \<sigma>_connected
          unfolding graphs_equal_in_U graph_V_equal_in_U
          unfolding induced_subgraph_V_def strongly_connected_def by simp blast
        done

      from U_in_Z have tangle_subgraph_subset:
        "tangle_subgraph \<alpha> U \<sigma>' \<subseteq> Restr (induced_subgraph (V_player \<alpha>) \<sigma>) Z"
        unfolding tangle_subgraph_is_restricted_ind_subgraph[OF U_in_V \<sigma>'_dom \<sigma>'_ran]
        unfolding \<sigma>'_dom
        unfolding restricted_strat_and_dom_subgraph_same_in_region[OF \<sigma>'_def] by blast
      have \<sigma>'_all_cycles_in_U_won:
        "\<forall>v\<in>U. \<forall>xs. cycle (tangle_subgraph \<alpha> U \<sigma>') v xs \<longrightarrow> player_wins_list \<alpha> xs"
        using subgraph_cycles_won_if_plays_won[OF tangle_subgraph_subset U_in_Z all_games_in_Z_won] .

      have \<sigma>'_tangle_strat: "tangle_strat \<alpha> U \<sigma>'"
        unfolding tangle_strat_iff Let_def
        apply (intro conjI)
        subgoal using \<sigma>'_strat .
        subgoal using \<sigma>'_dom by auto
        subgoal using \<sigma>'_ran .
        subgoal using \<sigma>'_connected .
        subgoal using \<sigma>'_all_cycles_in_U_won .
        done

      show ?thesis
        unfolding tangle_iff
        apply (rule exI[where x=\<alpha>]; intro conjI)
        subgoal using U_notempty .
        subgoal using U_in_V .
        subgoal sorry
        subgoal using \<sigma>'_tangle_strat by blast
        subgoal sorry
        done
    qed
  qed
qed

(** One step of the search algorithm preserves our invariant. *)
lemma search_step_I:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> search_I (R',Y')"
  using search_step_R_finite[of R Y R' Y']
    search_step_valid_subgame search_step_finite_Y[of R Y R' Y']
    search_step_tangles_Y[of R Y R' Y']
  unfolding search_I_def by blast

(** If two states are in the reflexive transitive closure of steps, then our invariant is preserved
    between them. *)
lemma search_step_rtranclp_I:
  "\<lbrakk>search_step\<^sup>*\<^sup>* S S'; search_I S\<rbrakk> \<Longrightarrow> search_I S'"
  apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal for y z using search_step_I[of "fst y" "snd y" "fst z" "snd z"] by simp
  done

(** The search algorithm applies the search_step until it reaches the end.
    We do not have to specify that ({},Y) is not in the domain of the step,
    as this follows automatically because no further steps exist from an empty R. *)
definition search :: "'v set \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "search R Y \<equiv> search_step\<^sup>*\<^sup>* (R,{}) ({},Y)"

(**
(** For every valid, non-empty subgame R, the search algorithm finds a Y. *)
lemma search_has_result:
  "\<lbrakk>R \<noteq> {}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)\<rbrakk> \<Longrightarrow> \<exists>Y. search R Y"
  unfolding search_def
  using search_step_terminates_with_Y by simp
*)

(** If we have a valid subgame R, then the invariant holds for it and an empty set. *)
lemma I_base_valid_subgame: "valid_subgame R \<Longrightarrow> search_I (R,{})"
  unfolding search_I_def
  using finite_subset[OF _ fin_V] by blast

(** Search preserves our invariant. *)
lemma search_preserves_I:
  "\<lbrakk>search R Y; search_I (R,{})\<rbrakk> \<Longrightarrow> search_I ({},Y)"
  unfolding search_def
  apply (induction rule: rtranclp_induct)
  subgoal by blast
  subgoal using search_step_rtranclp_I by blast
  done

(** If the initial R is a valid subgame, then search gives us a finite, non-empty Y that contains
    new tangles that were not included in T before. *)
lemma valid_subgame_search_correct:
  "\<lbrakk>valid_subgame R; search R Y\<rbrakk> \<Longrightarrow> finite Y \<and> Y \<noteq> {} \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T)"
  using search_I_correct[OF search_preserves_I[OF _ I_base_valid_subgame]] by simp
end (** End of context with fixed T. *)

end (** End of context paritygame *)

end
