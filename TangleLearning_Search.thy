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

lemma search_step_R_finite: "search_step (R,Y) (R',Y') \<Longrightarrow> finite R \<Longrightarrow> finite R'"
  apply (induction rule: search_step_induct)
  by blast

lemma search_step_valid_subgame:
  "search_step (R,Y) (R',Y') \<Longrightarrow> valid_subgame R \<Longrightarrow> valid_subgame R'"
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence tattr: "subgraph_tattr R \<alpha> T A Z \<sigma>" and
    R_in_V: "R \<subseteq> V" and
    R_valid_game: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
    by blast +

  from \<open>R' = R-Z\<close> \<open>valid_subgame R\<close> have R'_in_V: "R' \<subseteq> V" by auto

  moreover from R'_in_V \<open>R' = R-Z\<close> have "paritygame (Restr E R') (V\<inter>R') (V\<^sub>0\<inter>R')"
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
  "search_I \<equiv> \<lambda>(R,Y). finite R \<and> valid_subgame R \<and> finite Y \<and> (\<forall>U\<in>Y. \<exists>\<alpha>. tangle \<alpha> U)"

lemma search_step_finite_Y: "search_step (R,Y) (R',Y') \<Longrightarrow> search_I (R,Y) \<Longrightarrow> finite Y'"
  apply (induction rule: search_step_induct)
  using paritygame.tangle_attractor_finite[OF _ fin_T]
  unfolding search_I_def
  by force

lemma search_step_tangles_Y: "search_step (R,Y) (R',Y') \<Longrightarrow> search_I (R,Y)
  \<Longrightarrow> \<forall>U\<in>Y'. \<exists>\<alpha>. tangle \<alpha> U"
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence attr: "subgraph_tattr R \<alpha> T A Z \<sigma>" and
    A_def: "A = {v \<in> R. pr v = p}" and
    Ov_def: "Ov = {v \<in> V_player \<alpha> \<inter> A. E `` {v} \<inter> Z \<noteq> {}} \<union> {v \<in> V_opponent \<alpha> \<inter> A. E `` {v} \<inter> R \<subseteq> Z}" and
    Y'_def: "Y' = (if Ov \<noteq> {} then Y \<union> {S. bound_nt_bottom_SCC Z \<sigma> S} else Y)" and
    tangles_Y: "\<forall>U\<in>Y. \<exists>\<alpha>. tangle \<alpha> U" and
    R_in_V: "R \<subseteq> V" and
    R_valid_game: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
    unfolding search_I_def by auto

  from A_def
       paritygame.target_in_tangle_attractor[OF R_valid_game fin_T attr]
       paritygame.tangle_attractor_ss[OF R_valid_game fin_T attr]
  have A_in_Z: "A \<subseteq> Z" and Z_in_R: "Z \<subseteq> R" by blast+

  with R_in_V R_valid_game paritygame.axioms[OF R_valid_game]
       paritygame.tangle_attractor_strat[OF R_valid_game fin_T attr]
       restr_subgraph_V_player[of R \<alpha>] restr_ind_subgraph_V\<^sub>\<alpha>[of R "V_player \<alpha>" \<sigma>] have
    \<sigma>_strat: "paritygame.strategy_of_player (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> \<sigma>" and
    \<sigma>_dom: "dom \<sigma> = V_player \<alpha> \<inter> (Z-A)" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> Z" and
    \<sigma>_closed: "Restr (induced_subgraph (V_player \<alpha>) \<sigma>) R `` (Z-A) \<subseteq> Z" and
    \<sigma>_forces_A_or_wins: "\<forall>x\<in>Z. \<forall>xs ys.
      lasso_from_node (Restr (induced_subgraph (V_player \<alpha>) \<sigma>) R) x xs ys
        \<longrightarrow>set (xs @ ys) \<inter> A \<noteq> {} \<or> player_wins_list \<alpha> ys"
    by (auto simp: Int_absorb1)

  show ?case
  proof (rule ballI)
    fix U assume Y_in_Y': "U \<in> Y'"
    with Y'_def consider (old) "U \<in> Y" | (new) "U \<in> {S. bound_nt_bottom_SCC Z \<sigma> S}"
      by (auto split: if_splits)
    thus "\<exists>\<alpha>. tangle \<alpha> U" proof cases
      case old with tangles_Y show ?thesis by blast
    next
      case new
      hence U_in_Z: "U \<subseteq> Z" by blast
      with R_in_V Z_in_R have U_in_V: "U \<subseteq> V" by blast

      let ?\<sigma>_graph = "induced_subgraph (dom \<sigma>) \<sigma>"
      let ?\<sigma>_graph_V = "induced_subgraph_V (dom \<sigma>) \<sigma>"
      have fin_graph_ind: "finite_graph_V ?\<sigma>_graph ?\<sigma>_graph_V" by simp
      from new have U_notempty: "U \<noteq> {}" using finite_graph_V.nt_bottom_SCC_notempty by force
      (** TODO: make lemma for strong connectivity in nontrivial bottom SCCs *)
      from new have conn: "strongly_connected (Restr ?\<sigma>_graph U) (?\<sigma>_graph_V \<inter> U)"
        unfolding finite_graph_V.nt_bottom_SCC_def[OF fin_graph_ind]
        unfolding finite_graph_V.bottom_SCC_def[OF fin_graph_ind]
        unfolding finite_graph_V.SCC_def[OF fin_graph_ind] by blast

      from restr_subgraph_strategy_of_player[OF R_valid_game \<sigma>_strat]
      have "strategy_of (V_player \<alpha>) (\<sigma> |` U)"
        unfolding strategy_of_def
        using strat_le_E_of_strat[of "\<sigma> |` U" \<sigma>]
        by (auto simp: map_le_def)

      from U_in_Z have "dom (\<sigma> |` U) = U \<inter> V_player \<alpha>"
        using dom_restrict[of \<sigma> U]
        unfolding \<sigma>_dom
        apply safe
        subgoal by auto
        subgoal by blast
        (** I need to find a reason a successor exists, perhaps related to strong connectivity. *)
        subgoal for x apply (cases "x \<in> A")
          subgoal sorry
          subgoal by blast
          done
        done

      (** This is probably related to it being a strongly connected component. *)
      from U_in_Z \<sigma>_ran have "ran (\<sigma> |` U) \<subseteq> U" sorry

      have \<sigma>'_tangle_strat: "tangle_strat \<alpha> U (\<sigma> |` U)"
        unfolding tangle_strat_iff Let_def sorry

      show ?thesis
        unfolding tangle_iff
        apply (rule exI[where x=\<alpha>]; intro conjI)
        subgoal using U_notempty .
        subgoal using U_in_V .
        subgoal sorry
        subgoal using \<sigma>'_tangle_strat by blast
        done
    qed
  qed
qed

lemma search_step_I:
  "search_step (R,Y) (R',Y') \<Longrightarrow> search_I (R,Y) \<Longrightarrow> search_I (R',Y')"
  using search_step_R_finite search_step_valid_subgame search_step_finite_Y search_step_tangles_Y
  unfolding search_I_def
  apply clarify
  by metis

lemma "search_I ({},Y) \<Longrightarrow> finite Y \<and> Y \<noteq> {} \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U)"
  unfolding search_I_def
  apply simp
  sorry

lemma search_step_rtranclp_I: "search_step\<^sup>*\<^sup>* S S' \<Longrightarrow> search_I S \<Longrightarrow> search_I S'"
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
lemma search_preserves_I:
  "search R Y \<Longrightarrow> search_I (R,{}) \<Longrightarrow> search_I ({},Y)"
  unfolding search_def
  apply (induction rule: rtranclp_induct)
  subgoal unfolding search_I_def by blast
  subgoal using search_step_rtranclp_I by blast
  done
end (** End of context with fixed T. *)

end (** End of context paritygame *)

end