theory TangleLearning_Search
imports Main TangleAttractors TangleLearning
begin

definition test where "test = finite_graph_V_Succ.nt_bottom_SCC"

context paritygame begin

(** I may want to use this and move it to paritygames.thy.
    More, similar abbreviations for using concepts in a restricted subgame may be useful for
    legibility.*)
abbreviation (input) valid_subgame :: "'v set \<Rightarrow> bool" where
  "valid_subgame R \<equiv> R\<subseteq>V \<and> paritygame (Restr E R) R (V\<^sub>0\<inter>R)"

context
  fixes T :: "'v set set"
  assumes tangles_T: "\<forall>t\<in>T. tangle EVEN t \<or> tangle ODD t"
  assumes fin_T: "finite T"
begin

(** search_step represents a single iteration of the while-loop in the search algorithm. *)
inductive search_step ::
  "'v set \<times> 'v set  set \<Rightarrow> 'v set \<times> 'v set set \<Rightarrow> bool" where
  step: "\<lbrakk>R \<noteq> {}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R);
          p = pr_set R; \<alpha> = player_wins_pr p;
          A = {v. v \<in> R \<and> pr v = p};
          T\<^sub>\<alpha> = {t. t \<in> T \<and> paritygame.tangle (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> t};
          paritygame.tangle_attractor (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> T\<^sub>\<alpha> A Z \<sigma>;
          V\<^sub>\<alpha> = V_player \<alpha>; V\<^sub>\<beta> = V_opponent \<alpha>;
          Ov = {v. v \<in> V\<^sub>\<alpha>\<inter>A \<and> E `` {v} \<inter> Z \<noteq> {}} \<union> {v. v \<in> V\<^sub>\<beta>\<inter>A \<and> (E `` {v}) \<inter> R \<subseteq> Z};
          Y' = (if Ov \<noteq> {} then
            Y \<union> {S. S \<subseteq> Z \<and> finite_graph_V_Succ.nt_bottom_SCC (induced_subgraph V\<^sub>\<alpha> \<sigma>) (induced_subgraph_V V\<^sub>\<alpha> \<sigma>) S}
          else
            Y);
          R' = R-Z\<rbrakk> \<Longrightarrow> search_step (R,Y) (R',Y')"

(** If a step can be applied, both R and R' are subsets of V. *)
lemma search_step_R_in_V: "search_step S S' \<Longrightarrow> fst S \<subseteq> V \<and> fst S' \<subseteq> V"
  by (induction rule: search_step.induct) auto

(** If a step can be applied, both R and R' are finite. *)
lemma search_step_R_finite: "search_step S S' \<Longrightarrow> finite (fst S) \<and> finite (fst S')"
  using search_step_R_in_V finite_subset[OF _ fin_V] by auto

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

(** If a step is applied from some S, R' in S' is always a valid parity game. *)
lemma step_result_R_is_paritygame:
  "search_step S S' \<Longrightarrow> paritygame (Restr E (fst S')) (V\<inter>fst S') (V\<^sub>0\<inter>fst S')"
proof (induction rule: search_step.induct)
  case (step R p \<alpha> A T\<^sub>\<alpha> Z \<sigma> V\<^sub>\<alpha> V\<^sub>\<beta> Ov Y' Y R')
  (** We know that every tangle t in T\<^sub>\<alpha> is a tangle in the subgame of R, and that T\<^sub>\<alpha> is finite. *)
  from step(7) have tangles_T\<^sub>\<alpha>: "\<forall>t\<in>T\<^sub>\<alpha>. paritygame.tangle (Restr E R) (V \<inter> R) (V\<^sub>0 \<inter> R) pr \<alpha> t"
    by simp
  from step(7) have fin_T\<^sub>\<alpha>: "finite T\<^sub>\<alpha>"
    using finite_subset[OF _ fin_T] by simp
  (** We can write any instance of R-Z as R'. *)
  from step(13) have "(V \<inter> R-Z) = (V \<inter> R')" by blast
  moreover from step(13) have "(V\<^sub>0 \<inter> R-Z) = (V\<^sub>0 \<inter> R')" by blast
  (** If we restrict the already restricted graph R to R', we find that it is the same as
      restricting the whole graph to R'. *)
  moreover from step(13) have "(Restr (Restr E R) (V \<inter> R')) = Restr E R'" using E_in_V by auto
  (** Now, we can show that removing the tangle-attracted region from the graph yields a valid
      subgame. *)
  ultimately show ?case
    using paritygame.remove_tangle_attractor_subgame[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)] by auto
qed

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

lemma "search_step S S' \<Longrightarrow> snd S \<subseteq> snd S'"
  apply (induction rule: search_step.induct) by auto

(** TODO: invariant, prove property of Y on termination. *)
(** The current invariant states that everything contained in Y is a tangle.
    This should probably be restated to say that everything contained in Y is a tangle with its
    corresponding strategy. *)
definition search_I ::  "'v set \<times> 'v set set \<Rightarrow> bool" where
  "search_I S \<equiv> finite (snd S) \<and> (\<forall>U \<in> snd S. \<exists>\<alpha>. tangle \<alpha> U)"

lemma search_step_preserves_I:
  "search_step S S' \<Longrightarrow> search_I S \<Longrightarrow> search_I S'"
proof (induction rule: search_step.induct)
  case (step R p \<alpha> A T\<^sub>\<alpha> Z \<sigma> V\<^sub>\<alpha> V\<^sub>\<beta> Ov Y' Y R')
  (** We know that every tangle t in T\<^sub>\<alpha> is a tangle in the subgame of R, and that T\<^sub>\<alpha> is finite. *)
  from step(7) have tangles_T\<^sub>\<alpha>: "\<forall>t\<in>T\<^sub>\<alpha>. paritygame.tangle (Restr E R) (V \<inter> R) (V\<^sub>0 \<inter> R) pr \<alpha> t"
    by simp
  from step(7) have fin_T\<^sub>\<alpha>: "finite T\<^sub>\<alpha>"
    using finite_subset[OF _ fin_T] by simp

  from step(2,4,5) have player_wins_R: "player_winningP \<alpha> (pr_set (V \<inter> R))"
    unfolding player_wins_pr_def
    by (simp split: if_splits add: Int_absorb1)

  from step(2,4,6) have A': "A = {v \<in> V \<inter> R. pr v = pr_set (V \<inter> R)}"
    by (simp add: Int_absorb1)

  from paritygame.target_in_tangle_attractor[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)]
       paritygame.tangle_attractor_ss[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)] step(2,6)
  have A_in_Z: "A \<subseteq> Z" and Z_in_R: "Z \<subseteq> R" by blast+

  have "paritygame.strategy_of_player (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> \<sigma> = strategy_of_player \<alpha> \<sigma>"
    unfolding paritygame.strategy_of_player_def[OF step(3)] strategy_of_player_def
    unfolding arena.strategy_of_def[OF paritygame.axioms[OF step(3)]] strategy_of_def
    unfolding restr_subgraph_V_player[OF step(3)]
    unfolding E_of_strat_def
    apply (cases \<alpha>; clarsimp simp add: V\<^sub>1_def)
    xxx, sorry

  from Z_in_R paritygame.tangle_attractor_strat[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> step(8)] 
       restr_subgraph_V_player[OF step(3)] restr_ind_subgraph_V\<^sub>\<alpha>[OF paritygame.axioms[OF step(3)]]
  have
    \<sigma>_strat: "paritygame.strategy_of_player (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V_player \<alpha> \<inter> (Z-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> Z" and
    \<sigma>_closed_opp: "Restr (induced_subgraph (V_player \<alpha>) \<sigma>) R `` (Z-A) \<subseteq> Z" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>Z. \<forall>xs ys.
      lasso_from_node (Restr (induced_subgraph (V_player \<alpha>) \<sigma>) R) x xs ys
        \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys"
    by auto
   

  have "\<forall>v\<in>Z. \<forall>xs ys. lasso_from_node (Restr (induced_subgraph (V_player \<alpha>) \<sigma>) Z) v xs ys
          \<longrightarrow> player_wins_list \<alpha> ys"
  proof (rule ballI; intro allI; rule impI)
    fix v xs ys
    assume v_in_Z: "v \<in> Z" and
      lasso_v_xs_ys: "lasso_from_node (Restr (induced_subgraph (V_player \<alpha>) \<sigma>) Z) v xs ys"

    (** This should be a lemma. *)
    from \<open>Z\<subseteq>R\<close> have "(Restr (induced_subgraph (V_player \<alpha>) \<sigma>) Z) \<subseteq>
            (Restr (arena.induced_subgraph (Restr E R) (paritygame.V_player (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha>) \<sigma>) Z)"
      unfolding arena.induced_subgraph_def[OF paritygame.axioms[OF step(3)]] induced_subgraph_def
      using paritygame.V_player.simps[OF step(3)]
      by (cases \<alpha>; auto simp: V\<^sub>1_def arena.V\<^sub>1_def[OF paritygame.axioms[OF step(3)]])

    from paritygame.van_dijk_2[OF step(3) tangles_T\<^sub>\<alpha> fin_T\<^sub>\<alpha> player_wins_R A' step(8)]
      v_in_Z subgraph_lasso[OF this lasso_v_xs_ys]
    show "player_wins_list \<alpha> ys" by blast
  qed

  from step.prems have
    fin_Y: "finite Y" and
    tangles_Y: "\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U"
    unfolding search_I_def
    by auto

  show ?case
    unfolding search_I_def
  proof (intro conjI)
    from finite_subset[OF Z_in_R finite_subset[OF step(2) fin_V]]
    have fin_Z: "finite Z" .
    hence fin_Y'_additions:
      "finite {S. S \<subseteq> Z \<and> finite_graph_V_Succ.nt_bottom_SCC (induced_subgraph V\<^sub>\<alpha> \<sigma>) (induced_subgraph_V V\<^sub>\<alpha> \<sigma>) S}"
    by simp
    with fin_Y step(12) show "finite (snd (R',Y'))" by simp
  next
    show "\<forall>U\<in>snd (R', Y'). \<exists>\<alpha>. tangle \<alpha> U"
    proof (rule ballI; clarsimp)
      fix U
      assume U_in_Y': "U \<in> Y'"
      with step(12) consider
        (old) "U \<in> Y"
      | (new) "U \<in> {S. S \<subseteq> Z \<and> finite_graph_V_Succ.nt_bottom_SCC (induced_subgraph V\<^sub>\<alpha> \<sigma>) (induced_subgraph_V V\<^sub>\<alpha> \<sigma>) S}"
        by (auto split: if_splits)
      thus "\<exists>\<alpha>. tangle \<alpha> U" proof cases
        case old with tangles_Y show ?thesis by blast
      next
        case new
        hence U_in_Z: "U\<subseteq>Z" and
          SCC_U: "finite_graph_V_Succ.nt_bottom_SCC (induced_subgraph V\<^sub>\<alpha> \<sigma>) (induced_subgraph_V V\<^sub>\<alpha> \<sigma>) U"
          by auto

        (** This should be a lemma. In fact, there is a similar lemma, but it is limited to
            V\<^sub>\<alpha> = dom \<sigma>, which is not the case here. *)
        have "finite_graph_V_Succ (induced_subgraph V\<^sub>\<alpha> \<sigma>) (induced_subgraph_V V\<^sub>\<alpha> \<sigma>)"
        proof (unfold_locales)
          show "induced_subgraph V\<^sub>\<alpha> \<sigma> \<subseteq> induced_subgraph_V V\<^sub>\<alpha> \<sigma> \<times> induced_subgraph_V V\<^sub>\<alpha> \<sigma>"
            unfolding induced_subgraph_V_def by force
        next
          show "finite (induced_subgraph_V V\<^sub>\<alpha> \<sigma>)" by simp
        next
          show "\<And>v. v \<in> induced_subgraph_V V\<^sub>\<alpha> \<sigma> \<Longrightarrow> induced_subgraph V\<^sub>\<alpha> \<sigma> `` {v} \<noteq> {}"
          proof -
            fix v
            assume v_in_subgraph: "v \<in> induced_subgraph_V V\<^sub>\<alpha> \<sigma>"
            from paritygame.player_strat_in_E[OF step(3) \<sigma>_strat]
            have \<sigma>_edges_in_E: "E_of_strat \<sigma> \<subseteq> E" by simp

            consider (dom) "v \<in> dom \<sigma>" | (not_dom) "v \<notin> dom \<sigma>" by blast
            thus "induced_subgraph V\<^sub>\<alpha> \<sigma> `` {v} \<noteq> {}" proof cases
              case dom with \<sigma>_edges_in_E show ?thesis
                using edge_in_E_of_strat[of \<sigma>] strategy_to_ind_subgraph by blast
            next
              case not_dom
              from v_in_subgraph have "v \<in> V" using ind_subgraph_V_in_V by blast
              then obtain v' where "(v,v') \<in> E" using succ by blast
              consider (in_V\<^sub>\<alpha>) "v \<in> V\<^sub>\<alpha>" | (notin_V\<^sub>\<alpha>) "v \<notin> V\<^sub>\<alpha>" by blast
              thus ?thesis proof cases
                case in_V\<^sub>\<alpha>
                with Z_in_R not_dom have "v \<notin> (Z-A)"
                  unfolding step(9) \<sigma>_dom by blast
                show ?thesis sorry
              next
                case notin_V\<^sub>\<alpha>
                from ind_subgraph_notin_dom[OF \<open>(v,v')\<in>E\<close> notin_V\<^sub>\<alpha>]
                show ?thesis by blast
              qed
            qed
          qed
        qed
        have "U \<noteq> {}" sorry

        
        show ?thesis
          unfolding tangle_iff tangle_strat_iff sorry
      qed
    qed
  qed
qed

lemma search_step_rtranclp_preserves_I:
  "search_step\<^sup>*\<^sup>* S S' \<Longrightarrow> search_I S \<Longrightarrow> search_I S'"
  apply (induction rule: rtranclp_induct)
  using search_step_preserves_I by auto

(** The search algorithm applies the search_step until it reaches the end.
    We do not have to specify that ({},Y) is not in the domain of the step,
    as this follows automatically because no further steps exist from an empty R. *)
definition search :: "'v set \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "search R Y \<equiv> search_step\<^sup>*\<^sup>* (R,{}) ({},Y)"

(** For every valid, non-empty subgame R, the search algorithm finds a Y. *)
lemma search_has_result:
  "\<lbrakk>R \<noteq> {}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)\<rbrakk> \<Longrightarrow> \<exists>Y. search R Y"
  unfolding search_def
  using search_step_terminates_with_Y by simp

lemma search_preserves_I:
  "search R Y \<Longrightarrow> search_I ({},Y)"
  unfolding search_def
  apply (induction rule: rtranclp_induct)
  subgoal unfolding search_I_def by simp
  subgoal using search_step_rtranclp_preserves_I by blast
  done

lemma search_finds_tangles:
  shows "search R Y \<Longrightarrow> Y \<noteq> {} \<and> finite Y \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U)"
  apply (intro conjI)
  subgoal sorry
  subgoal using search_preserves_I unfolding search_I_def by simp
  subgoal using search_preserves_I unfolding search_I_def by simp
  done
end (** End of context with fixed T. *)

end (** End of context paritygame *)

end