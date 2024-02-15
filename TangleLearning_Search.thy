theory TangleLearning_Search
imports Main PredicateTermination TangleAttractors TangleLearning
begin

type_synonym 'a search_state = "'a set \<times> 'a set set"

context paritygame begin

(** I may want to use this and move it to paritygames.thy.
    More, similar abbreviations for using concepts in a restricted subgame may be useful for
    legibility.*)

abbreviation (input) bound_nt_bottom_SCC :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v set \<Rightarrow> bool" where
  "bound_nt_bottom_SCC Z \<sigma> S \<equiv> S \<subseteq> Z \<and>
    finite_graph_V.nt_bottom_SCC (induced_subgraph \<sigma>) (induced_subgraph_V \<sigma>) S"

abbreviation (input) subgraph_tattr
  :: "'v set \<Rightarrow> player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "subgraph_tattr R \<alpha> T A Z \<sigma> \<equiv> paritygame.tangle_attractor (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> T A Z \<sigma>"

context
  fixes T :: "'v set set"
  assumes fin_T: "finite T"
  assumes tangles_T: "\<forall>t\<in>T. tangle EVEN t \<or> tangle ODD t"
  assumes open_tangles_T: "\<forall>t\<in>T. tangle \<alpha> t \<longrightarrow> E `` (t \<inter> V_opponent \<alpha>) - t \<noteq> {}"
begin

(** search_step represents a single iteration of the while-loop in the search algorithm. *)
inductive search_step :: "'v search_state \<Rightarrow> 'v search_state \<Rightarrow> bool" where
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

(** The search algorithm applies the search_step until it reaches the end.
    We do not have to specify that ({},Y) is not in the domain of the step,
    as this follows automatically because no further steps exist from an empty R. *)
definition search :: "'v set \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "search R Y \<equiv> search_step\<^sup>*\<^sup>* (R,{}) ({},Y)"


section \<open>Invariant\<close>
(** TODO: invariant, prove property of Y on termination. *)
(** The current invariant states that everything contained in Y is a tangle.
    This should probably be restated to say that everything contained in Y is a tangle with its
    corresponding strategy. *)
(**
definition search_I ::  "'v set \<times> 'v set set \<Rightarrow> bool" where
  "search_I S \<equiv> finite (snd S) \<and> (\<forall>U \<in> snd S. \<exists>\<alpha>. tangle \<alpha> U) \<and> (fst S={} \<longrightarrow> \<dots>)"
*)

definition search_I :: "'v search_state \<Rightarrow> bool" where
  "search_I \<equiv> \<lambda>(R,Y). finite R \<and> valid_subgame R \<and> finite Y \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U)"

(** If we end with an empty region, then we have a finite, non-empty Y containing new tangles that
    were not included in T before, as specified by our invariant. *)
lemma search_I_correct:
  "search_I ({},Y) \<Longrightarrow> finite Y \<and> Y \<noteq> {} \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T)"
  unfolding search_I_def apply simp oops

(** If the initial R is finite, then R' is finite after a step. *)
lemma search_step_R_finite:
  "\<lbrakk>search_step (R,Y) (R',Y'); finite R\<rbrakk> \<Longrightarrow> finite R'"
  by (induction rule: search_step_induct) blast

(** If the initial R is a valid subgame, then R' is a valid subgame after a step. *)
lemma search_step_valid_subgame:
  "\<lbrakk>search_step (R,Y) (R',Y'); valid_subgame R\<rbrakk> \<Longrightarrow> valid_subgame R'"
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence tattr: "subgraph_tattr R \<alpha> T A Z \<sigma>" by blast
  from \<open>valid_subgame R\<close> interpret R_game: paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" ..

  from \<open>R' = R-Z\<close> \<open>valid_subgame R\<close> have "R' \<subseteq> V" by auto

  moreover from \<open>R' \<subseteq> V\<close> \<open>R' = R-Z\<close> have "paritygame (Restr E R') (V\<inter>R') (V\<^sub>0\<inter>R')"
    using R_game.remove_tangle_attractor_subgame[OF fin_T tattr]
    by (simp add: Times_Int_Times Int_assoc Int_absorb1 Int_Diff)

  ultimately show ?case ..
qed

(** If our invariant holds for a state, a step of the search algorithm gives us a finite Y'. *)
lemma search_step_finite_Y:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> finite Y'"
  unfolding search_I_def split
  apply (induction rule: search_step_induct)
  using paritygame.tangle_attractor_finite[OF _ fin_T]
  by force

(** If our invariant holds for a state, a step of the search algorithm gives us a Y' with new tangles
    that were not included in T before. *)
lemma search_step_tangles_Y:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> \<forall>U \<in> Y'. \<exists>\<alpha>. tangle \<alpha> U"
  unfolding search_I_def split
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence attr: "subgraph_tattr R \<alpha> T A Z \<sigma>" and
    A_def: "A = {v \<in> R. pr v = p}" and
    Ov_def: "Ov = {v \<in> V_player \<alpha> \<inter> A. E `` {v} \<inter> Z \<noteq> {}}
      \<union> {v \<in> V_opponent \<alpha> \<inter> A. E `` {v} \<inter> R \<subseteq> Z}" and
    Y'_def: "Y' = (if Ov \<noteq> {} then Y \<union> {S. bound_nt_bottom_SCC Z \<sigma> S} else Y)" and
    tangles_Y: "\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U" and
    R_in_V: "R \<subseteq> V" and
    R_valid_game: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
    by auto
  from R_valid_game interpret R_game:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" by blast

  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?G\<sigma>_V = "induced_subgraph_V \<sigma>"

  from A_def \<open>R \<subseteq> V\<close>
    R_game.target_in_tangle_attractor[OF fin_T attr]
    R_game.tangle_attractor_in_V[OF fin_T attr]
  have "A \<subseteq> Z" and "Z \<subseteq> R" and "A \<subseteq> R" by auto
  with R_in_V R_game.player_strat_in_E
    R_game.tangle_attractor_strat[OF fin_T attr] have
    \<sigma>_strat: "strategy_of (V_player \<alpha> \<inter> Z) \<sigma>" and
    \<sigma>_dom: "dom \<sigma> \<subseteq> V_player \<alpha> \<inter> Z" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> Z" and
    \<sigma>_partially_closed: "(Restr ?G\<sigma> R) `` (Z-A) \<subseteq> Z" and
    \<sigma>_forces_A_or_wins:
      "\<forall>x\<in>Z. \<forall>xs ys. lasso (Restr ?G\<sigma> R) x xs ys
        \<longrightarrow>set (xs @ ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys" and
    \<sigma>_path_to_A:
      "\<forall>x\<in>Z. \<exists>y\<in>A. \<exists>xs. path (Restr ?G\<sigma> R) x xs y"
    unfolding restr_subgraph_V_player[OF R_valid_game]
      restr_ind_subgraph[OF paritygame.axioms[OF R_valid_game]]
    unfolding strategy_of_player_def strategy_of_def by auto

  have all_games_in_Z_won:
    "\<forall>v\<in>Z. \<forall>xs ys. lasso (Restr ?G\<sigma> Z) v xs ys
      \<longrightarrow> player_wins_list \<alpha> ys"
  proof -
    from \<open>R\<subseteq>V\<close> step(2,3) have "player_winningP \<alpha> (pr_set (V \<inter> R))"
      by (cases \<alpha>; simp add: player_wins_pr_def Int_absorb1 split: if_splits)
    moreover from \<open>R\<subseteq>V\<close> step(2,4) have "A = {v \<in> V \<inter> R. pr v = pr_set (V \<inter> R)}"
      by (simp add: Int_absorb1)
    ultimately show ?thesis
      using R_game.van_dijk_2[OF fin_T _ _ attr]
      unfolding restr_subgraph_V_player[OF R_valid_game]
        restr_ind_subgraph[OF paritygame.axioms[OF R_valid_game]]
        Restr_subset[OF \<open>Z\<subseteq>R\<close>] by simp
  qed

  show ?case
  proof (rule ballI)
    fix U assume U_in_Y': "U \<in> Y'"
    with Y'_def consider (old) "U \<in> Y" | (new) "U \<in> {S. bound_nt_bottom_SCC Z \<sigma> S}"
      by (auto split: if_splits)
    thus "\<exists>\<alpha>. tangle \<alpha> U" proof cases
      case old with tangles_Y show ?thesis by blast
    next
      case new
      from new have "U \<subseteq> Z" by blast
      with \<open>Z\<subseteq>R\<close> have "U \<subseteq> R" by blast
      with \<open>R\<subseteq>V\<close> have "U \<subseteq> V" by blast
      from finite_subset[OF this fin_V] have fin_U: "finite U" .
      from new have "U \<noteq> {}"
        using finite_graph_V.nt_bottom_SCC_notempty by force

      interpret fin_graph_\<sigma>: finite_graph_V ?G\<sigma> ?G\<sigma>_V by simp

      from new \<open>U\<subseteq>V\<close> have \<sigma>_connected: "strongly_connected (Restr ?G\<sigma> U) U"
        using fin_graph_\<sigma>.nt_bottom_SCC_strongly_connected fin_graph_\<sigma>.nt_bottom_SCC_in_V
        by (simp add: Int_absorb1)
      from new have \<sigma>_U_succ_in_U: "\<forall>v\<in>U. \<exists>v'\<in>U. (v,v') \<in> ?G\<sigma>"
        using fin_graph_\<sigma>.nt_bottom_SCC_succ_in_SCC by blast

      define \<sigma>' where "\<sigma>' = \<sigma> |` U"
      let ?G\<sigma>' = "induced_subgraph \<sigma>'"
      let ?G\<sigma>'_V = "induced_subgraph_V \<sigma>'"
      have \<sigma>'_le_\<sigma>: "\<sigma>' \<subseteq>\<^sub>m \<sigma>" by (auto simp: \<sigma>'_def map_le_def)

      from restricted_strat_subgraph_same_in_region[OF \<sigma>'_def]
      have graphs_equal_in_U:
        "Restr ?G\<sigma> U = Restr ?G\<sigma>' U" .
      from restricted_strat_subgraph_V_same_in_region[OF \<sigma>'_def] new
      have graph_V_equal_in_U: "?G\<sigma>'_V \<inter> U = ?G\<sigma>_V \<inter> U"
        using fin_graph_\<sigma>.nt_bottom_SCC_in_V by blast

      from \<sigma>_U_succ_in_U graphs_equal_in_U have \<sigma>'_U_succ_in_U:
        "\<forall>v\<in>U. \<exists>v'\<in>U. (v, v') \<in> ?G\<sigma>'" by blast

      from \<sigma>_strat have \<sigma>'_strat: "strategy_of (V_player \<alpha>) \<sigma>'"
        using strat_le_E_of_strat[OF \<sigma>'_le_\<sigma>]
        unfolding strategy_of_def \<sigma>'_def by auto

      have \<sigma>'_dom: "dom \<sigma>' = U \<inter> V_player \<alpha>"
      proof
        from \<sigma>_dom show "dom \<sigma>' \<subseteq> U \<inter> V_player \<alpha>" unfolding \<sigma>'_def by auto
      next
        {
          fix x assume assm: "x \<in> V_player \<alpha> \<inter> A \<inter> U"
          with \<open>U\<subseteq>R\<close> \<sigma>'_U_succ_in_U
          have "Restr E R `` {x} \<inter> U \<noteq> {}"
            using ind_subgraph by fast
          with assm \<open>U\<subseteq>Z\<close> have "x \<in> dom \<sigma>'"
            using R_game.tangle_attractor_strat_in_dom_A[OF fin_T attr]
            unfolding restr_subgraph_V_player[OF R_valid_game] \<sigma>'_def by auto
        }
        moreover
        {
          fix x assume "x \<in> V_player \<alpha> \<inter> (U-A)"
          with \<open>U\<subseteq>Z\<close> \<open>Z\<subseteq>R\<close> have "x \<in> dom \<sigma>'"
            using R_game.tangle_attractor_strat_in_dom_not_A[OF fin_T attr, of x]
            unfolding restr_subgraph_V_player[OF R_valid_game] \<sigma>'_def by fastforce
        }
        ultimately show "U \<inter> V_player \<alpha> \<subseteq> dom \<sigma>'" by blast
      qed

      from \<sigma>'_U_succ_in_U have \<sigma>'_ran: "ran \<sigma>' \<subseteq> U"
        unfolding \<sigma>'_def
        using ran_restrictD[of _ \<sigma> U] ind_subgraph_to_strategy by fastforce

      from \<sigma>_connected have \<sigma>'_connected:
        "strongly_connected (tangle_subgraph \<alpha> U \<sigma>') U"
        unfolding tangle_subgraph_is_restricted_ind_subgraph[OF \<open>U\<subseteq>V\<close> \<sigma>'_dom \<sigma>'_ran]
        by (simp add: graphs_equal_in_U)

      from \<open>U\<subseteq>Z\<close> have tangle_subgraph_subset:
        "tangle_subgraph \<alpha> U \<sigma>' \<subseteq> Restr ?G\<sigma> Z"
        unfolding tangle_subgraph_is_restricted_ind_subgraph[OF \<open>U\<subseteq>V\<close> \<sigma>'_dom \<sigma>'_ran]
        unfolding \<sigma>'_dom
        unfolding restricted_strat_and_dom_subgraph_same_in_region[OF \<sigma>'_def] by blast
      have \<sigma>'_all_cycles_in_U_won:
        "\<forall>v\<in>U. \<forall>xs. cycle (tangle_subgraph \<alpha> U \<sigma>') v xs \<longrightarrow> player_wins_list \<alpha> xs"
        using subgraph_cycles_won_if_plays_won[OF tangle_subgraph_subset \<open>U\<subseteq>Z\<close> all_games_in_Z_won] .

      have \<sigma>'_tangle_strat: "tangle_strat \<alpha> U \<sigma>'"
        unfolding tangle_strat_iff Let_def
        apply (intro conjI)
        subgoal using \<sigma>'_strat .
        subgoal using \<sigma>'_dom by auto
        subgoal using \<sigma>'_ran .
        subgoal using \<sigma>'_connected .
        subgoal using \<sigma>'_all_cycles_in_U_won .
        done


      have winning_pr_U: "player_winningP \<alpha> (pr_set U)"
      proof -
        have U_has_A: "U \<inter> A \<noteq> {}"
        proof -
          (** From all nodes in Z, we have a path to some node in A.
              This means that from all nodes in A, we also have a path to some
              node in A. Therefore, any nontrivial bottom SCC in Z should contain
              at least one node in A.

              The last step in the former reasoning needs some more work. *)
          have "\<forall>x\<in>U. \<exists>y\<in>A. \<exists>xs. path (Restr ?G\<sigma>' U) x xs y"
          proof (rule ballI)
            fix x assume "x \<in> U"
            show "\<exists>y\<in>A. \<exists>xs. path (Restr ?G\<sigma>' U) x xs y" oops
          qed
          show ?thesis oops
        qed
        hence "pr_set U = pr_set R"
          unfolding step
          using pr_set_exists[OF fin_U \<open>U\<noteq>{}\<close>]
          using pr_le_pr_set[OF fin_U]
          using R_game.pr_le_pr_set_V
          apply (safe; clarsimp simp: Int_absorb1[OF \<open>R\<subseteq>V\<close>])
          using le_antisym[of "pr v" "pr_set U" for v]
          using \<open>U\<subseteq>R\<close> subset_eq
          by metis
        thus ?thesis
          unfolding step player_wins_pr_def by simp
      qed

      show ?thesis
        unfolding tangle_iff
        apply (rule exI[where x=\<alpha>]; intro conjI)
        subgoal using \<open>U\<noteq>{}\<close> .
        subgoal using \<open>U\<subseteq>V\<close> .
        subgoal using winning_pr_U .
        subgoal using \<sigma>'_tangle_strat by blast
        done
    qed
  qed
qed

(** One step of the search algorithm preserves our invariant. *)
lemma search_step_preserves_I:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> search_I (R',Y')"
  using search_step_R_finite[of R Y R' Y']
    search_step_valid_subgame[of R Y R' Y']
    search_step_finite_Y[of R Y R' Y']
    search_step_tangles_Y[of R Y R' Y']
  unfolding search_I_def split by fast

(** If two states are in the reflexive transitive closure of steps, then our invariant is preserved
    between them. *)
lemma search_step_rtranclp_preserves_I:
  "\<lbrakk>search_step\<^sup>*\<^sup>* (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> search_I (R',Y')"
  apply (induction rule: rtranclp_induct2)
  using search_step_preserves_I by blast+

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
  using search_step_rtranclp_preserves_I by simp

(** If the initial R is a valid subgame, then search gives us a finite, non-empty Y that contains
    new tangles that were not included in T before. *)
theorem valid_subgame_search_correct:
  "\<lbrakk>valid_subgame R; search R Y\<rbrakk> \<Longrightarrow> finite Y \<and> Y \<noteq> {} \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T)"
  using search_I_correct[OF search_preserves_I[OF _ I_base_valid_subgame]] oops


section \<open>Termination\<close>

lemma search_step_R_decreasing:
  "\<lbrakk>search_step (R,Y) (R',Y'); valid_subgame R\<rbrakk> \<Longrightarrow> R' \<subset> R"
  apply (induction rule: search_step_induct)
  subgoal for R
    using pr_set_exists[OF finite_subset[OF _ fin_V, of R]]
    using paritygame.target_in_tangle_attractor[OF _ fin_T]
    by blast
  done

lemma search_step_wfP_I:
  "wfP (\<lambda>s' s. search_step s s' \<and> search_I s)"
  unfolding wfP_def
  apply (rule wf_subset[of "inv_image (finite_psubset) (\<lambda>(R,Y). R)"]; clarsimp)
  subgoal for R' Y' R Y
    using search_step_R_decreasing[of R Y R' Y']
    unfolding search_I_def by fast
  done

lemma search_step_final_empty_R:
  assumes I: "search_I (R,Y)"
  assumes final: "\<not>Domainp search_step (R,Y)"
  shows "R = {}"
proof (rule ccontr)
  assume "R \<noteq> {}"
  with I have "valid_subgame R"
    unfolding search_I_def split by blast
  then interpret subgame: paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R"
    by blast
  obtain p \<alpha> A Z \<sigma> Ov Y' R' where
    "p = pr_set R" and
    "\<alpha> = player_wins_pr p" and
    "A = {v. v \<in> R \<and> pr v = p}" and
    "subgraph_tattr R \<alpha> T A Z \<sigma>" and
    "Ov = {v \<in> V_player \<alpha> \<inter> A. E `` {v} \<inter> Z \<noteq> {}}
        \<union> {v \<in> V_opponent \<alpha> \<inter> A. E `` {v} \<inter> R \<subseteq> Z}" and
    "Y' = (if Ov \<noteq> {} then Y \<union> {S. bound_nt_bottom_SCC Z \<sigma> S} else Y)" and
    "R' = R-Z"
    using subgame.tangle_attractor_exists[OF fin_T] by presburger
  with \<open>R\<noteq>{}\<close> have "search_step (R,Y) (R',Y')"
    using search_step.step[of R p \<alpha> A Z \<sigma> Ov Y' Y R'] by fast
  hence "Domainp search_step (R,Y)" by blast
  with final show False by blast
qed

lemma search_step_terminates:
  assumes "valid_subgame R"
  shows "trm search_step (R,{})"
  apply (rule wfP_I_terminates[where I=search_I])
  using I_base_valid_subgame[OF assms(1)]
  using search_step_preserves_I
  using search_step_wfP_I
  unfolding search_I_def split by blast+

lemma search_step_exists:
  assumes "valid_subgame R"
  shows "\<exists>Y. search R Y"
  using trm_final_state[OF search_step_terminates[OF assms]]
  using I_base_valid_subgame[OF assms]
  using search_step_final_empty_R[OF search_step_rtranclp_preserves_I]
  unfolding search_def by fast
end (** End of context with fixed T. *)
end (** End of context paritygame. *)

end
