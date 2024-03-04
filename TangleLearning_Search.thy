theory TangleLearning_Search
imports Main PredicateTermination TangleAttractors
begin

type_synonym 'a search_state = "'a set \<times> 'a set set"

context paritygame begin

(** I may want to use this and move it to paritygames.thy.
    More, similar abbreviations for using concepts in a restricted subgame may be useful for
    legibility.*)
abbreviation (input) bound_nt_bottom_SCC
  :: "'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> 'v set \<Rightarrow> bool"
where
  "bound_nt_bottom_SCC R Z \<sigma> S \<equiv> S \<subseteq> Z \<and>
    finite_graph_V.nt_bottom_SCC (Restr (induced_subgraph \<sigma>) R) (induced_subgraph_V \<sigma> \<inter> R) S"

abbreviation (input) subgraph_tattr
  :: "'v set \<Rightarrow> player \<Rightarrow> 'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> bool"
where
  "subgraph_tattr R \<alpha> T A Z \<sigma> \<equiv>
    paritygame.tangle_attractor (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) pr \<alpha> T A Z \<sigma>"


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
    Y' = (if Ov \<noteq> {} then Y \<union> {S. bound_nt_bottom_SCC R Z \<sigma> S} else Y);
    R' = R-Z\<rbrakk> \<Longrightarrow> search_step (R,Y) (R',Y')"

(** This induction rule allows us to use explicit pairs in induction proofs. *)
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
definition search_I :: "'v search_state \<Rightarrow> bool" where
  "search_I \<equiv> \<lambda>(R,Y). finite R \<and> valid_subgame R \<and> finite Y \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U)
    \<and> (\<forall>U \<in> Y. U \<notin> T)"

subsection \<open>Invariant Preservation\<close>
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

(** All games that stay in Z in our step are won by \<alpha>.
    This is lemma 2 in Van Dijk's correctness proof. *)
lemma search_step_games_in_Z_won:
  assumes valid_subgame_R: "valid_subgame R"
  assumes p_def: "p = pr_set R"
  assumes \<alpha>_def: "\<alpha> = player_wins_pr p"
  assumes A_def: "A = {v \<in> R. pr v = p}"
  assumes attr: "subgraph_tattr R \<alpha> T A Z \<sigma>"
  shows "\<forall>x\<in>Z. \<forall>xs ys. lasso (Restr (induced_subgraph \<sigma>) Z) x xs ys
          \<longrightarrow> player_wins_list \<alpha> ys"
proof (intro ballI allI impI)
  (** R is a valid subgame of V. We make that explicit for convenience. *)
  from valid_subgame_R interpret R_game:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" by blast
  from valid_subgame_R have "R\<subseteq>V" by simp
  (** Shorthand for the induced subgraph of \<sigma>. *)
  let ?G\<sigma> = "induced_subgraph \<sigma>"
  (** The subgraph of \<sigma> in R is the same as the subgraph of \<sigma> in V
      restricted to the region R. *)
  have R_subgraph_eq: "R_game.induced_subgraph \<sigma> = Restr ?G\<sigma> R"
    using restr_ind_subgraph[OF R_game.arena_axioms] .

  (** We fix our lasso in Z. *)
  fix x xs ys
  assume lasso: "lasso (Restr ?G\<sigma> Z) x xs ys"
     and "x \<in> Z"
  (** This lasso also exists in the whole graph. *)
  from restr_V_lasso[OF lasso] have
    ys_in_Z: "set ys \<subseteq> Z" and
    lasso_\<sigma>: "lasso ?G\<sigma> x xs ys"
    by blast+
  (** Since Z is part of R, the lasso also stays in R. *)
  with \<open>R\<subseteq>V\<close> have ys_in_R: "set ys \<subseteq> R"
    using R_game.tangle_attractor_in_V[OF fin_T attr]
    unfolding A_def by blast
  (** We need only the loop ys, so we take the y it starts from. *)
  from lasso_loop[OF lasso_\<sigma>] obtain y where
    lasso_ys: "lasso ?G\<sigma> y [] ys" and
    "y \<in> set ys" "ys \<noteq> []"
    by fastforce
  (** This y lies in both Z and R. *)
  with ys_in_Z ys_in_R have
    "y\<in>Z" "y\<in>R" by blast+
  (** Now either ys intersects with A, or it does not. *)
  consider (A_notin_ys) "set ys \<inter> A = {}"
         | (A_in_ys) "set ys \<inter> A \<noteq> {}" by blast
  thus "player_wins_list \<alpha> ys" proof cases
    (** If ys does not intersect with A, it stays in a tangle
        for \<alpha>, and is thus won, because Z is a tangle attractor. *)
    case A_notin_ys
    with \<open>y\<in>Z\<close> show ?thesis
      using R_game.tangle_attractor_strat[OF fin_T attr]
      using lasso_restr_V[OF lasso_ys _ ys_in_R]
      by (auto simp: R_subgraph_eq)
  next
    (** If A is part of ys, the highest priority in it must be p. *)
    case A_in_ys
    have "pr_list ys = pr_set R"
    proof (rule antisym)
      (** p is the top priority in R, so any cycle in R
          must have its highest priority less than or
          equal to p. *)
      from ys_in_R \<open>R\<subseteq>V\<close> \<open>ys\<noteq>[]\<close>
      show "pr_list ys \<le> pr_set R"
        using R_game.pr_list_le_pr_set_V
        by (simp add: Int_absorb1)
    next
      (** We know a node with priority p is part of ys,
          so it must be less than or equal to the highest
          priority in the list. *)
      from A_in_ys ys_in_R p_def A_def \<open>R\<subseteq>V\<close>
      show "pr_set R \<le> pr_list ys"
        using R_game.pr_V_in_list
        by (auto simp: Int_absorb1)
    qed
    (** We know that \<alpha> wins p. *)
    moreover from \<open>R\<subseteq>V\<close> p_def \<alpha>_def
    have "player_winningP \<alpha> (pr_set (V \<inter> R))"
      by (simp add: player_wins_pr_def Int_absorb1)
    (** We know that the highest priority in ys is p,
        and we know p is won by \<alpha>, proving our thesis. *)
    ultimately show ?thesis
      by (simp add: Int_absorb1[OF \<open>R\<subseteq>V\<close>])
  qed
qed

(** If our invariant holds for a state, a step of the search algorithm gives us a Y' that contains
    tangles. *)
lemma search_step_tangles_Y:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> \<forall>U \<in> Y'. \<exists>\<alpha>. tangle \<alpha> U"
  unfolding search_I_def split
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence attr: "subgraph_tattr R \<alpha> T A Z \<sigma>" and
    p_def: "p = pr_set R" and
    \<alpha>_def: "\<alpha> = player_wins_pr p" and
    A_def: "A = {v \<in> R. pr v = p}" and
    Y'_def: "Y' = (if Ov \<noteq> {} then Y \<union> {S. bound_nt_bottom_SCC R Z \<sigma> S} else Y)" and
    tangles_Y: "\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U" and
    R_in_V: "R \<subseteq> V" and
    R_valid_game: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
    by auto
  then interpret R_game:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" by blast

  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?V\<sigma> = "induced_subgraph_V \<sigma>"

  have R_game_V_player_eq:
    "R_game.V_player \<alpha> = V_player \<alpha> \<inter> R"
    using restr_subgraph_V_player[OF R_game.paritygame_axioms] .
  have R_game_G\<sigma>_eq:
    "R_game.induced_subgraph \<sigma> = Restr ?G\<sigma> R"
    using restr_ind_subgraph[OF R_game.arena_axioms] .

  from A_def \<open>R\<subseteq>V\<close>
    R_game.target_in_tangle_attractor[OF fin_T attr]
    R_game.tangle_attractor_in_V[OF fin_T attr]
  have "A \<subseteq> Z" and "Z \<subseteq> R" and "A \<subseteq> R" by auto
  with R_in_V R_game.player_strat_in_E
    R_game.tangle_attractor_strat[OF fin_T attr] have
    \<sigma>_strat: "strategy_of (V_player \<alpha> \<inter> Z) \<sigma>" and
    \<sigma>_dom: "dom \<sigma> \<subseteq> V_player \<alpha> \<inter> Z" and
    \<sigma>_path_to_A:
      "\<forall>x\<in>Z. \<exists>y\<in>A. \<exists>xs. path (Restr ?G\<sigma> R) x xs y"
    unfolding R_game_V_player_eq R_game_G\<sigma>_eq
    unfolding strategy_of_player_def strategy_of_def by auto

  from \<open>R\<subseteq>V\<close> R_valid_game p_def \<alpha>_def A_def attr have in_Z_won:
    "\<forall>x\<in>Z. \<forall>xs ys. lasso (Restr ?G\<sigma> Z) x xs ys \<longrightarrow> player_wins_list \<alpha> ys"
    using search_step_games_in_Z_won by auto

  show ?case
  proof (rule ballI)
    fix U assume U_in_Y': "U \<in> Y'"
    with Y'_def consider (old) "U \<in> Y"
                       | (new) "U \<in> {S. bound_nt_bottom_SCC R Z \<sigma> S}"
      by (auto split: if_splits)
    thus "\<exists>\<alpha>. tangle \<alpha> U" proof cases
      case old with tangles_Y show ?thesis by blast
    next
      case new
      interpret fin_graph_\<sigma>: finite_graph_V "Restr ?G\<sigma> R" "?V\<sigma> \<inter> R"
        unfolding induced_subgraph_V_def
        by (unfold_locales) force+

      from new have "U \<subseteq> Z" by simp
      with \<open>Z\<subseteq>R\<close> have "U \<subseteq> R" by simp
      from new have fin_U: "finite U"
        using fin_graph_\<sigma>.nt_bottom_SCC_finite by simp
      from new have \<sigma>_connected:
        "strongly_connected (Restr ?G\<sigma> U) U"
        using fin_graph_\<sigma>.nt_bottom_SCC_strongly_connected
        using Int_absorb1[OF \<open>U\<subseteq>R\<close>] Int_assoc[of _ "R\<times>R" "U\<times>U"]
        by (simp add: Times_Int_Times) fastforce
      from new have \<sigma>_U_closed: "(Restr ?G\<sigma> R) `` U \<subseteq> U"
        using fin_graph_\<sigma>.nt_bottom_SCC_closed by simp
      from new have \<sigma>_U_succ_in_U: "\<forall>v\<in>U. \<exists>v'\<in>U. (v,v') \<in> ?G\<sigma>"
        using fin_graph_\<sigma>.nt_bottom_SCC_succ_in_SCC by blast

      show ?thesis
        unfolding tangle_iff
      proof (rule exI[where x=\<alpha>]; intro conjI)
        from new show "U \<noteq> {}"
          using fin_graph_\<sigma>.nt_bottom_SCC_notempty by blast

        from new have "U \<subseteq> Z" by blast
        with \<open>Z\<subseteq>R\<close> have "U \<subseteq> R" by blast
        with \<open>R\<subseteq>V\<close> show "U \<subseteq> V" by blast

        show "player_winningP \<alpha> (pr_set U)"
        proof -
          have "U \<inter> A \<noteq> {}"
          proof (rule ccontr; simp)
            assume "U \<inter> A = {}"
            moreover
            {
              fix x assume "x \<in> U"
              with \<sigma>_path_to_A \<open>U\<subseteq>Z\<close> obtain xs y where
                y_in_A: "y \<in> A" and
                path: "path (Restr ?G\<sigma> R) x xs y" by blast

              from path_closed_dest[OF \<open>x\<in>U\<close> \<sigma>_U_closed path] y_in_A
              have "\<exists>x\<in>U. x \<in> A" by auto
            }
            moreover note \<open>U\<noteq>{}\<close>
            ultimately show False by blast
          qed
          with \<open>U\<subseteq>R\<close> \<open>U\<subseteq>V\<close> have "pr_set U = pr_set R"
            using pr_le_pr_set[OF fin_U] R_game.pr_set_le_pr_set_V[OF _ \<open>U\<noteq>{}\<close>]
            by (simp add: A_def p_def Int_absorb1[OF \<open>R\<subseteq>V\<close>]) force
          thus ?thesis
            unfolding \<alpha>_def p_def
            by (simp add: player_wins_pr_def)
        qed

        define \<sigma>' where "\<sigma>' = \<sigma> |` U"
        let ?G\<sigma>' = "induced_subgraph \<sigma>'"
        let ?V\<sigma>' = "induced_subgraph_V \<sigma>'"
        have \<sigma>'_le_\<sigma>: "\<sigma>' \<subseteq>\<^sub>m \<sigma>" by (auto simp: \<sigma>'_def map_le_def)

        from restricted_strat_subgraph_same_in_region[OF \<sigma>'_def]
        have graphs_equal_in_U:
          "Restr ?G\<sigma> U = Restr ?G\<sigma>' U" .
        from restricted_strat_subgraph_V_same_in_region[OF \<sigma>'_def] new
        have graph_V_equal_in_U: "?V\<sigma>' \<inter> U = ?V\<sigma> \<inter> U"
          using fin_graph_\<sigma>.nt_bottom_SCC_in_V by blast

        from \<sigma>_U_succ_in_U graphs_equal_in_U
        have \<sigma>'_U_succ_in_U:
          "\<forall>v\<in>U. \<exists>v'\<in>U. (v, v') \<in> ?G\<sigma>'" by blast

        show "\<exists>\<sigma>. tangle_strat \<alpha> U \<sigma>"
          unfolding tangle_strat_iff Let_def
        proof (rule exI[where x=\<sigma>']; intro conjI)
          show \<sigma>'_strat: "strategy_of (V_player \<alpha>) \<sigma>'"
            using strat_le_E_of_strat[OF \<sigma>'_le_\<sigma>]
            using \<sigma>'_def \<sigma>_strat strategy_of_def by force

          show \<sigma>'_dom: "dom \<sigma>' = U \<inter> V_player \<alpha>"
          proof
            from \<sigma>_dom show "dom \<sigma>' \<subseteq> U \<inter> V_player \<alpha>"
              unfolding \<sigma>'_def by auto
          next
            {
              fix x assume assm: "x \<in> V_player \<alpha> \<inter> A \<inter> U"
              with \<open>U\<subseteq>R\<close> have "Restr E R `` {x} \<inter> U \<noteq> {}"
                using ind_subgraph \<sigma>'_U_succ_in_U by fast
              with assm \<open>U\<subseteq>Z\<close> have "x \<in> dom \<sigma>'"
                using R_game.tangle_attractor_strat_in_dom_A[OF fin_T attr]
                unfolding restr_subgraph_V_player[OF R_valid_game] \<sigma>'_def
                by auto
            }
            moreover
            {
              fix x assume "x \<in> V_player \<alpha> \<inter> (U-A)"
              with \<open>U\<subseteq>Z\<close> \<open>Z\<subseteq>R\<close> have "x \<in> dom \<sigma>'"
                using R_game.tangle_attractor_strat_in_dom_not_A[OF fin_T attr, of x]
                unfolding restr_subgraph_V_player[OF R_valid_game] \<sigma>'_def
                by fastforce
            }
            ultimately show "U \<inter> V_player \<alpha> \<subseteq> dom \<sigma>'" by blast
          qed

          from \<sigma>'_U_succ_in_U show \<sigma>'_ran: "ran \<sigma>' \<subseteq> U"
            unfolding \<sigma>'_def
            using ran_restrictD[of _ \<sigma> U] ind_subgraph_to_strategy
            by fastforce

          from \<sigma>_connected show \<sigma>'_conn:
            "strongly_connected (tangle_subgraph \<alpha> U \<sigma>') U"
            unfolding tangle_subgraph_is_restricted_ind_subgraph[OF \<open>U\<subseteq>V\<close> \<sigma>'_dom \<sigma>'_ran]
            by (simp add: graphs_equal_in_U)

          from \<open>U\<subseteq>Z\<close> have tangle_subgraph_subset:
            "tangle_subgraph \<alpha> U \<sigma>' \<subseteq> Restr ?G\<sigma> Z"
            unfolding tangle_subgraph_is_restricted_ind_subgraph[OF \<open>U\<subseteq>V\<close> \<sigma>'_dom \<sigma>'_ran]
            unfolding restricted_strat_and_dom_subgraph_same_in_region[OF \<sigma>'_def] by blast
          show \<sigma>'_wins:
            "\<forall>v\<in>U. \<forall>xs. cycle (tangle_subgraph \<alpha> U \<sigma>') v xs \<longrightarrow> player_wins_list \<alpha> xs"
          proof -
            from \<open>U\<subseteq>Z\<close> have tangle_subgraph_subset:
              "tangle_subgraph \<alpha> U \<sigma>' \<subseteq> Restr ?G\<sigma> Z"
              unfolding tangle_subgraph_is_restricted_ind_subgraph[OF \<open>U\<subseteq>V\<close> \<sigma>'_dom \<sigma>'_ran]
              unfolding restricted_strat_and_dom_subgraph_same_in_region[OF \<sigma>'_def] by blast
            from in_Z_won show ?thesis
              using subsetD[OF \<open>U\<subseteq>Z\<close>] subgraph_path[OF tangle_subgraph_subset]
              unfolding lasso_def cycle_def by blast
          qed
        qed
      qed
    qed
  qed
qed

(** TODO: change this to say that the regions are \<alpha>-maximal for \<alpha>. *)
lemma search_step_escapes_in_higher_region:
  assumes valid_R: "valid_subgame R"
  assumes attr: "subgraph_tattr R \<alpha> T A Z \<sigma>"
  assumes SCC: "bound_nt_bottom_SCC R Z \<sigma> U"
  shows "escapes \<alpha> U \<subseteq> V - R"
proof -
  from valid_R interpret R_game:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" by blast
  from valid_R have "R \<subseteq> V" by simp

  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?V\<sigma> = "induced_subgraph_V \<sigma>"

  interpret \<sigma>_subgraph: finite_graph_V "Restr ?G\<sigma> R" "?V\<sigma> \<inter> R"
    unfolding induced_subgraph_V_def
    by (unfold_locales) force+

  have "(Restr E R) `` (U \<inter> V_opponent \<alpha>) \<subseteq> U"
  proof -
    from R_game.tangle_attractor_strat[OF fin_T attr]
    have \<sigma>_dom_no_opp: "dom \<sigma> \<inter> V_opponent \<alpha> = {}"
      unfolding R_game.V_player_opposite_V_opponent[of \<alpha>]
      unfolding restr_subgraph_V_opponent[OF R_game.paritygame_axioms]
      by auto
    with SCC show ?thesis
      using \<sigma>_subgraph.nt_bottom_SCC_closed
      unfolding induced_subgraph_def by fast
  qed

  moreover from SCC have "U \<subseteq> R"
    using \<sigma>_subgraph.nt_bottom_SCC_in_V by blast

  ultimately show ?thesis
    by (auto simp: escapes_eq)
qed

lemma "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y);
        \<forall>v\<in>V-R. \<exists>R2 \<alpha> A X \<sigma>. v \<in> R2 \<and> X \<subseteq> V-R \<and> subgraph_tattr R2 \<alpha> T A X \<sigma>\<rbrakk>
          \<Longrightarrow> \<forall>v\<in>V-R'. \<exists>R2 \<alpha> A X \<sigma>. v \<in> R2 \<and> X \<subseteq> V-R' \<and> subgraph_tattr R2 \<alpha> T A X \<sigma>"
  unfolding search_I_def split
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  hence "R' \<subset> R"
    using pr_set_exists[OF finite_subset[OF _ fin_V, of R]]
    using paritygame.target_in_tangle_attractor[OF _ fin_T]
    by blast

  from step interpret R_game:
    paritygame "Restr E R" "V \<inter> R" "V\<^sub>0 \<inter> R" by simp
  show ?case proof (rule ballI)
    fix v assume "v \<in> V-R'"
    with \<open>R' \<subset> R\<close> consider "v \<in> V-R" | "v \<in> R" by blast
    thus "\<exists>R2 \<alpha> A X \<sigma>. v \<in> R2 \<and> X \<subseteq> V-R' \<and> subgraph_tattr R2 \<alpha> T A X \<sigma>"
    proof cases
      case 1
      with step(10) obtain R2 \<alpha> A X \<sigma> where
        "v \<in> R2 \<and> X \<subseteq> V - R \<and> subgraph_tattr R2 \<alpha> T A X \<sigma>"
        by meson
      with \<open>R'\<subset>R\<close> show ?thesis by blast
    next
      case 2
      from step have "A\<subseteq>R"
        using R_game.target_in_tangle_attractor[OF fin_T step(5)]
        by blast
      from step have "R\<subseteq>V" by simp
      with \<open>A\<subseteq>R\<close> have "A\<subseteq>V" by simp
      from step have "Z \<subseteq> R"
        using R_game.tangle_attractor_in_V[OF fin_T step(5)]
        by blast
      show ?thesis
        apply (rule exI[where x=R])
        apply (rule exI[where x=\<alpha>])
        apply (rule exI[where x=A])
        apply (rule exI[where x=Z])
        apply (rule exI[where x=\<sigma>])
        apply (intro conjI)
        subgoal using 2 by simp
        subgoal using \<open>Z\<subseteq>R\<close> \<open>R'=R-Z\<close> \<open>R\<subseteq>V\<close> by blast
        subgoal using step by simp
        done
    qed
  qed
qed

lemma search_step_Y_new:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> \<forall>U\<in>Y'. U \<notin> T"
  unfolding search_I_def split
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  from step interpret R_game:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" by fast

  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?V\<sigma> = "induced_subgraph_V \<sigma>"

  interpret fin_graph_\<sigma>: finite_graph_V "Restr ?G\<sigma> R" "?V\<sigma> \<inter> R"
    unfolding induced_subgraph_V_def
    by (unfold_locales) force+

  show ?case proof (rule ballI; rule ccontr; simp)
    fix U assume "U \<in> Y'" "U \<in> T"
    with step(7) consider (old) "U \<in> Y"
                        | (new) "U \<in> {S. bound_nt_bottom_SCC R Z \<sigma> S}"
      by (auto split: if_splits)
    thus False proof cases
      case old with step \<open>U\<in>T\<close> show ?thesis by blast
    next
      case new
      hence SCC: "bound_nt_bottom_SCC R Z \<sigma> U" and "U\<subseteq>Z" by blast+
      with step search_step_escapes_in_higher_region
      have "escapes \<alpha> U \<subseteq> V - R" by presburger
      moreover have "\<exists>\<alpha>2 A2 X \<sigma>2. escapes \<alpha> U \<subseteq> X \<and> tangle_attractor \<alpha>2 T A2 X \<sigma>2" sorry
      then obtain \<alpha>2 A2 X \<sigma>2 where
        "tangle_attractor \<alpha>2 T A2 X \<sigma>2" and esc: "escapes \<alpha> U \<subseteq> X" by blast
      hence max: "\<alpha>_max \<alpha>2 T X"
        by (simp add: fin_T tangle_attractor_is_\<alpha>_max)
      with esc show ?thesis
        using \<alpha>_max_no_tattr_succs[OF fin_T]
        sorry

    qed
  qed
qed

(** One step of the search algorithm preserves our invariant. *)
lemma search_step_preserves_I:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> search_I (R',Y')"
  using search_step_R_finite[of R Y R' Y']
  using search_step_valid_subgame[of R Y R' Y']
  using search_step_finite_Y[of R Y R' Y']
  using search_step_tangles_Y[of R Y R' Y']
  unfolding search_I_def split sorry by fast

(** If two states are in the reflexive transitive closure of steps, then our invariant is preserved
    between them. *)
lemma search_step_rtranclp_preserves_I:
  "\<lbrakk>search_step\<^sup>*\<^sup>* (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> search_I (R',Y')"
  apply (induction rule: rtranclp_induct2)
  using search_step_preserves_I by blast+

(** If we have a valid nonempty subgame R, then the invariant holds for it and an empty Y. *)
lemma search_I_base: "valid_subgame R \<Longrightarrow> search_I (R,{})"
  unfolding search_I_def split
  using finite_subset[OF _ fin_V] by blast

(** Search preserves our invariant. *)
lemma search_preserves_I:
  "\<lbrakk>search R Y; search_I (R,{})\<rbrakk> \<Longrightarrow> search_I ({},Y)"
  unfolding search_def
  using search_step_rtranclp_preserves_I by simp


subsection \<open>Emptiness of Y'\<close>
lemma search_step_last:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y); R' = {}\<rbrakk> \<Longrightarrow> Y' \<noteq> {}"
  unfolding search_I_def split
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?V\<sigma> = "induced_subgraph_V \<sigma>"

  from step have R_valid_game: "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)" by blast
  then interpret R_game: paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" .

  from step have attr: "R_game.tangle_attractor \<alpha> T A Z \<sigma>" by simp
  from step have "R \<subseteq> V" by blast
  from step have "R = Z"
    using R_game.tangle_attractor_in_V[OF fin_T] by blast
  from step have "A \<subseteq> Z"
    using R_game.target_in_tangle_attractor[OF fin_T] by blast
  from step have "A \<noteq> {}"
    using pr_set_exists by fastforce
  from \<open>A\<subseteq>Z\<close> \<open>A\<noteq>{}\<close>

  have A_succs_in_Z: "(E `` A) \<inter> Z \<subseteq> Z" "(E `` A) \<inter> Z \<noteq> {}"
    using R_game.succ R_game.E_closed_V
    unfolding Int_absorb1[OF \<open>R\<subseteq>V\<close>]
    unfolding \<open>R=Z\<close>
    by blast+

  with \<open>R\<noteq>{}\<close> \<open>R\<subseteq>V\<close> \<open>A\<noteq>{}\<close> \<open>A\<subseteq>Z\<close>
  have "Ov \<noteq> {}"
    unfolding step(6) \<open>R=Z\<close>
    by (cases \<alpha>; simp) blast+
  with step have Y'_def:
    "Y' = Y \<union> {U. bound_nt_bottom_SCC R Z \<sigma> U}"
    by auto

  have "\<exists>U. bound_nt_bottom_SCC R Z \<sigma> U"
  proof -
    from \<open>R=Z\<close> R_game.tangle_attractor_strat[OF fin_T attr] have
      \<sigma>_strat: "strategy_of (V_player \<alpha>) \<sigma>" and
      \<sigma>_ran: "ran \<sigma> \<subseteq> Z" and
      \<sigma>_closed: "(Restr ?G\<sigma> Z) `` Z \<subseteq> Z" and
      \<sigma>_path_to_A: "\<forall>x\<in>Z. \<exists>y\<in>A. \<exists>xs. path (Restr ?G\<sigma> Z) x xs y"
      unfolding restr_subgraph_V_player[OF R_valid_game]
      unfolding restr_ind_subgraph[OF paritygame.axioms[OF R_valid_game]]
      using restr_subgraph_strategy_of_player[OF R_valid_game]
      by auto

    then interpret \<sigma>_graph:
      finite_graph_V_succ ?G\<sigma> ?V\<sigma>
      unfolding strategy_of_def
      apply unfold_locales
      by (auto simp: finite_graph_V.E_in_V ind_subgraph_succ)

    have \<sigma>_dom: "dom \<sigma> = V_player \<alpha> \<inter> Z"
    proof
      show "dom \<sigma> \<subseteq> V_player \<alpha> \<inter> Z"
        using R_game.tangle_attractor_strat[OF fin_T attr]
        unfolding restr_subgraph_V_player[OF R_valid_game] by simp
    next
      from \<open>R=Z\<close> \<open>R\<subseteq>V\<close> show "V_player \<alpha> \<inter> Z \<subseteq> dom \<sigma>"
        using R_game.succ
        using R_game.tangle_attractor_strat_in_dom_A[OF fin_T attr]
        using R_game.tangle_attractor_strat_in_dom_not_A[OF fin_T attr]
        unfolding restr_subgraph_V_player[OF R_valid_game]
        by blast
    qed

    hence G\<sigma>_is_E_outside_Z: "Restr ?G\<sigma> (-Z) = Restr E (-Z)"
      unfolding induced_subgraph_def E_of_strat_def
      by blast

    from \<sigma>_strat have "EV (E_of_strat \<sigma>) \<subseteq> ?V\<sigma>"
      unfolding strategy_of_def induced_subgraph_V_def induced_subgraph_def E_of_strat_def
      by auto

    moreover have "dom \<sigma> \<subseteq> EV (E_of_strat \<sigma>)"
      unfolding E_of_strat_def dom_def by force

    ultimately have dom_in_V: "dom \<sigma> \<subseteq> ?V\<sigma>"
      by auto

    from \<open>R=Z\<close> R_game.tangle_attractor_strat[OF fin_T attr]
    have \<sigma>_edges_in_Z: "E_of_strat \<sigma> \<subseteq> Restr E Z"
      unfolding R_game.strategy_of_player_def R_game.strategy_of_def
      by auto

    from restr_ind_subgraph[OF paritygame.axioms[OF R_valid_game]]
    have subgames_equal_in_Z: "R_game.induced_subgraph \<sigma> = Restr ?G\<sigma> Z"
      by (simp add: \<open>R=Z\<close>)

    have subgame_V_equal_in_Z:
      "R_game.induced_subgraph_V \<sigma> = ?V\<sigma> \<inter> Z"
    proof
      show "R_game.induced_subgraph_V \<sigma> \<subseteq> ?V\<sigma> \<inter> Z"
        unfolding R_game.induced_subgraph_V_def induced_subgraph_V_def
        unfolding subgames_equal_in_Z by auto
    next
      show "?V\<sigma> \<inter> Z \<subseteq> R_game.induced_subgraph_V \<sigma>"
      proof
        fix x assume x_in_\<sigma>_V_Int_Z: "x \<in> ?V\<sigma> \<inter> Z"
        hence "x \<in> Z" by auto

        consider (in_dom) "x \<in> dom \<sigma>" | (notin_dom) "x \<notin> dom \<sigma>" by blast
        thus "x \<in> R_game.induced_subgraph_V \<sigma>" proof cases
          case in_dom
          with \<sigma>_ran obtain y where
            "y \<in> Z" "(x,y) \<in> E_of_strat \<sigma>"
            unfolding E_of_strat_def ran_def by blast
          hence "(x,y) \<in> Restr (R_game.induced_subgraph \<sigma>) Z"
            unfolding subgames_equal_in_Z induced_subgraph_def
            using \<sigma>_edges_in_Z by blast
          thus ?thesis
            unfolding R_game.induced_subgraph_V_def by force
        next
          case notin_dom
          from \<open>x\<in>Z\<close> \<open>R\<subseteq>V\<close> \<open>R=Z\<close> obtain y where
            "(x,y) \<in> Restr E Z"
            using R_game.succ[of x] by blast
          with \<open>R=Z\<close> have "(x,y) \<in> Restr (R_game.induced_subgraph \<sigma>) Z"
            using R_game.ind_subgraph_notin_dom[OF _ notin_dom] by blast
          thus ?thesis
            unfolding R_game.induced_subgraph_V_def by force
        qed
      qed
    qed

    interpret \<sigma>_graph_Z:
      finite_graph_V_succ "Restr ?G\<sigma> Z" "?V\<sigma> \<inter> Z"
    proof (unfold_locales)
      show "Restr ?G\<sigma> Z \<subseteq> (?V\<sigma> \<inter> Z) \<times> (?V\<sigma> \<inter> Z)"
        using \<sigma>_graph.E_in_V by blast
      show "finite (?V\<sigma> \<inter> Z)" by blast
      show "\<And>v. v \<in> ?V\<sigma> \<inter> Z \<Longrightarrow> Restr ?G\<sigma> Z `` {v} \<noteq> {}"
        using \<open>R=Z\<close> R_game.ind_subgraph_succ \<sigma>_edges_in_Z
        using subgame_V_equal_in_Z subgames_equal_in_Z by blast
    qed

    from \<open>R=Z\<close> interpret \<sigma>_graph_R:
      finite_graph_V_succ "Restr ?G\<sigma> R" "?V\<sigma> \<inter> R"
      using \<sigma>_graph_Z.finite_graph_V_succ_axioms by blast


    from \<open>R\<noteq>{}\<close> \<open>R\<subseteq>V\<close> \<open>R=Z\<close> have "Restr E Z `` Z \<noteq> {}"
      using R_game.succ by blast

    from \<open>A\<noteq>{}\<close> obtain a where "a \<in> A" by blast
    with \<open>A\<subseteq>Z\<close> \<open>R=Z\<close> have "a \<in> R" by blast
    have "a \<in> induced_subgraph_V \<sigma> \<inter> Z"
    proof -
      consider (dom) "a \<in> dom \<sigma>" | (not_dom) "a \<notin> dom \<sigma>" by blast
      thus ?thesis proof cases
        case dom with \<open>A\<subseteq>Z\<close> \<open>a\<in>A\<close> dom_in_V
        show ?thesis  by auto
      next
        case not_dom with \<open>a\<in>R\<close> show ?thesis
          unfolding induced_subgraph_V_def
          using ind_subgraph_notin_dom[OF _ not_dom]
          using R_game.succ[of a]
          apply (clarsimp simp add: Int_absorb1[OF \<open>R\<subseteq>V\<close>])
          using image_iff \<open>R=Z\<close> by fastforce
      qed
    qed
    from \<sigma>_graph_Z.cycle_always_exists[OF this]
    obtain y ys where cycle: "cycle (Restr ?G\<sigma> Z) y ys"
      unfolding reachable_cycle_def by blast
    hence "set ys \<noteq> {}" by auto
    have ys_conn: "strongly_connected (Restr (Restr ?G\<sigma> Z) (set ys)) (set ys)"
      using cycle_strongly_connected[OF cycle] by blast

    from \<sigma>_graph_R.nt_bottom_SCC_ex obtain U where
      "\<sigma>_graph_R.nt_bottom_SCC U"
      using \<open>a \<in> induced_subgraph_V \<sigma> \<inter> Z\<close> \<open>R=Z\<close> by blast

    thus ?thesis
      using \<sigma>_graph_R.nt_bottom_SCC_in_V \<open>R=Z\<close> by blast
  qed
  thus ?case
    unfolding Y'_def by simp
qed

lemma search_step_rtranclp_last:
  "\<lbrakk>search_step\<^sup>*\<^sup>* (R,Y) (R',Y'); search_I (R,Y); R \<noteq> {}; R' = {}\<rbrakk> \<Longrightarrow> Y' \<noteq> {}"
  apply (induction rule: rtranclp_induct2)
  by (auto simp: search_step_last search_step_rtranclp_preserves_I)

lemma search_step_nonempty_R:
  "\<lbrakk>search R Y; valid_subgame R; R \<noteq> {}\<rbrakk> \<Longrightarrow> Y \<noteq> {}"
  unfolding search_def
  using search_step_rtranclp_last search_I_base by simp

lemma search_step_notempty[simp]: "\<not>search_step ({},Y) (R',Y')"
  by (simp add: search_step.simps)

lemma search_step_rtranclp_empty_R: "\<lbrakk>search_step\<^sup>*\<^sup>* (R,Y) (R',Y'); R = {}\<rbrakk> \<Longrightarrow> Y = Y'"
  by (induction rule: converse_rtranclp_induct2) auto

lemma search_empty_R:
  "\<lbrakk>search {} Y\<rbrakk> \<Longrightarrow> Y = {}"
  unfolding search_def
  using search_step_rtranclp_empty_R by blast

subsection \<open>Correctness\<close>
(** If we end with an empty region, then we have a finite, non-empty Y containing new tangles that
    were not included in T before, as specified by our invariant. *)
lemma search_I_correct:
  "search_I ({},Y) \<Longrightarrow> finite Y \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T)"
  unfolding search_I_def by simp

(** If the initial R is a valid subgame, then search gives us a finite, non-empty Y that contains
    new tangles that were not included in T before. *)
theorem search_correct:
  "\<lbrakk>valid_subgame R; search R Y\<rbrakk>
    \<Longrightarrow> finite Y \<and> (R \<noteq> {} \<longleftrightarrow> Y \<noteq> {}) \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U \<and> U \<notin> T)"
  using search_I_correct[OF search_preserves_I[OF _ search_I_base]]
  apply (safe; clarsimp)
  subgoal using search_step_nonempty_R by fast
  subgoal using search_empty_R by fastforce
  done


section \<open>Termination\<close>
lemma search_step_R_decreasing:
  "\<lbrakk>search_step (R,Y) (R',Y'); valid_subgame R\<rbrakk> \<Longrightarrow> R' \<subset> R"
  apply (induction rule: search_step_induct)
  subgoal for R
    using pr_set_exists[OF finite_subset[OF _ fin_V, of R]]
    using paritygame.target_in_tangle_attractor[OF _ fin_T]
    by blast
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
  from \<open>R\<noteq>{}\<close> obtain R' Y' where
    "search_step (R,Y) (R',Y')"
    using subgame.tangle_attractor_exists[OF fin_T]
    using search_step.step[of R _ _ _ _ _ _ _ Y]
    by clarsimp fastforce
  hence "Domainp search_step (R,Y)" by blast
  with final show False by blast
qed

lemma search_step_wfP_I:
  "wfP (\<lambda>s' s. search_step s s' \<and> search_I s)"
  unfolding wfP_def
  apply (rule wf_subset[of "inv_image (finite_psubset) (\<lambda>(R,Y). R)"]; clarsimp)
  using search_step_R_decreasing
  unfolding search_I_def by fast

lemma search_step_terminates:
  assumes "valid_subgame R"
  shows "trm search_step (R,{})"
  apply (rule wfP_I_terminates[where I=search_I])
  using search_I_base[OF assms]
  using search_step_preserves_I
  using search_step_wfP_I
  unfolding search_I_def split by blast+

lemma search_step_exists:
  assumes "valid_subgame R"
  shows "\<exists>Y. search R Y"
  using trm_final_state[OF search_step_terminates[OF assms]]
  using search_I_base[OF assms]
  using search_step_final_empty_R[OF search_step_rtranclp_preserves_I]
  unfolding search_def by fast
end (** End of context with fixed T. *)
end (** End of context paritygame. *)

end
