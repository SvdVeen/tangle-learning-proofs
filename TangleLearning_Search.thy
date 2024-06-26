theory TangleLearning_Search
imports Main PredicateTermination TangleAttractors
begin
(**
  Authors:
    - Suzanne van der Veen
    - Peter Lammich
    - Tom van Dijk

  This theory focuses on the search algorithm.
*)
chapter \<open>The Search Algorithm\<close>
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
inductive search_step
  :: "'v search_state \<Rightarrow> 'v search_state \<Rightarrow> bool"
where step:
  "\<lbrakk>R \<noteq> {};
    p = pr_set R; \<alpha> = player_wins_pr p;
    A = {v. v \<in> R \<and> pr v = p};
    subgraph_tattr R \<alpha> T A Z \<sigma>;
    Ov = {v \<in> V_player \<alpha> \<inter> A. E `` {v} \<inter> Z = {}}
       \<union> {v \<in> V_opponent \<alpha> \<inter> A. \<not>E `` {v} \<inter> R \<subseteq> Z};
    Y' = (if Ov = {} then Y \<union> {S. bound_nt_bottom_SCC R Z \<sigma> S} else Y);
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
  "search_I \<equiv> \<lambda>(R,Y). valid_subgame R \<and> finite Y \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U)"
(**    \<and> (\<forall>U \<in> Y. U \<notin> T)"*)

(** If we end with an empty region, then we have a finite, non-empty Y containing new tangles that
    were not included in T before, as specified by our invariant. *)
lemma search_I_correct:
  "search_I ({},Y) \<Longrightarrow> finite Y \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U)"
  unfolding search_I_def split by fast

(** If we have a valid nonempty subgame R, then the invariant holds for it and an empty Y. *)
lemma search_I_base: "valid_subgame R \<Longrightarrow> search_I (R,{})"
  unfolding search_I_def split by blast

subsection \<open>Invariant Preservation\<close>
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
  using finite_subset[OF _ fin_V] by force

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
    "y \<in> set ys" "ys \<noteq> []" by fastforce
  (** This y lies in Z. *)
  with ys_in_Z have "y \<in> Z" by blast
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
    with ys_in_R \<open>R\<subseteq>V\<close> have "pr_list ys = p"
      using R_game.pr_V_in_list
      by (auto simp: A_def p_def Int_absorb1)
    (** We know that \<alpha> wins p. *)
    moreover have "player_winningP \<alpha> p"
      by (auto simp: \<alpha>_def player_wins_pr_def)
    (** We know that the highest priority in ys is p,
        and we know p is won by \<alpha>, proving our thesis. *)
    ultimately show ?thesis by simp
  qed
qed

(** If our invariant holds for a state, a step of the search algorithm gives us a Y'
    that contains tangles. *)
lemma search_step_tangles_Y:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> \<forall>U \<in> Y'. \<exists>\<alpha>. tangle \<alpha> U"
  unfolding search_I_def split
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  (** R is a parity game, and we will use its lemmas in the proof. *)
  then interpret R_game:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" by blast
  (** Shorthand for the subgame of \<sigma> and its vertices. *)
  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?V\<sigma> = "induced_subgraph_V \<sigma>"
  (** We will use these to simplify some properties:
      - V_player in R is equal to V_player restricted to R.
      - The induced subgraph of \<sigma> in R is equal to itself in the whole graph
        restricted to R. *)
  have R_game_V_player_eq: "R_game.V_player \<alpha> = V_player \<alpha> \<inter> R"
    using restr_subgraph_V_player[OF R_game.paritygame_axioms] .
  have R_game_G\<sigma>_eq: "R_game.induced_subgraph \<sigma> = Restr ?G\<sigma> R"
    using restr_ind_subgraph[OF R_game.arena_axioms] .
  (** We name these properties to make them easier to access in the proof. *)
  from step have
    p_def: "p = pr_set R" and
    \<alpha>_def: "\<alpha> = player_wins_pr p" and
    A_def: "A = {v \<in> R. pr v = p}" and
    attr: "R_game.tangle_attractor \<alpha> T A Z \<sigma>" and
    Y'_def: "Y' = (if Ov = {} then Y \<union> {S. bound_nt_bottom_SCC R Z \<sigma> S} else Y)" and
    tangles_Y: "\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U" and
    R_in_V: "R \<subseteq> V"
    by auto
  (** Since A is part of a tangle attractor Z, which is part of R,
      A is part of Z and R. *)
  from A_def \<open>R\<subseteq>V\<close> have "A \<subseteq> Z" "Z \<subseteq> R" "A \<subseteq> R"
    using R_game.target_in_tangle_attractor[OF fin_T attr]
    using R_game.tangle_attractor_in_V[OF fin_T attr]
    by auto
  (** Because Z is an attractor with strategy \<sigma>, \<sigma> is a strategy of the player in Z,
      its domain contains \<alpha>-nodes in Z, and there exists a path to A in the subgame of \<sigma>
      within R. *)
  have \<sigma>_strat: "strategy_of (V_player \<alpha> \<inter> Z) \<sigma>"
   and \<sigma>_dom: "dom \<sigma> \<subseteq> V_player \<alpha> \<inter> Z"
   and \<sigma>_path_to_A: "\<forall>x\<in>Z. \<exists>y\<in>A. \<exists>xs. path (Restr ?G\<sigma> R) x xs y"
    using R_game.player_strat_in_E
    using R_game.tangle_attractor_strat[OF fin_T attr]
    unfolding R_game_V_player_eq R_game_G\<sigma>_eq
    unfolding strategy_of_player_def strategy_of_def
    by force+
  (** Per our previous lemma, all plays that stay in Z are won under \<sigma>. *)
  from step have in_Z_won:
    "\<forall>x\<in>Z. \<forall>xs ys. lasso (Restr ?G\<sigma> Z) x xs ys \<longrightarrow> player_wins_list \<alpha> ys"
    using search_step_games_in_Z_won by auto
  (** Now, we show that all U in Y' are tangles. *)
  show ?case proof (rule ballI)
    fix U assume "U \<in> Y'"
    (** Distinguish between a U from Y and a U from Y'-Y. *)
    with Y'_def consider
      (existing_U) "U \<in> Y" | (new_U) "U \<in> {S. bound_nt_bottom_SCC R Z \<sigma> S}"
      by (auto split: if_splits)
    thus "\<exists>\<alpha>. tangle \<alpha> U" proof cases
      (** If U was part of Y, it is a tangle because the invariant holds for (R,Y). *)
      case existing_U with tangles_Y show ?thesis by blast
    next
      case new_U
      (** We will need lemmas from the finite graph that is the subgame of \<sigma> in R. *)
      interpret \<sigma>_graph: finite_graph_V "Restr ?G\<sigma> R" "?V\<sigma> \<inter> R"
        unfolding induced_subgraph_V_def
        by unfold_locales force+
      (** U is part of Z because it is a bottom SCC within Z,
          and it is part of R because Z is part of R. *)
      from new_U \<open>Z\<subseteq>R\<close> have "U \<subseteq> Z" "U \<subseteq> R" by auto
      (** Because it is an SCC, it is finite. *)
      from new_U have fin_U: "finite U"
        using \<sigma>_graph.nt_bottom_SCC_finite by simp
      (** Because U is a bottom SCC, it is strongly connected. *)
      from new_U have \<sigma>_U_connected:
        "strongly_connected (Restr ?G\<sigma> U) U"
        using \<sigma>_graph.nt_bottom_SCC_strongly_connected
        using Int_absorb1[OF \<open>U\<subseteq>R\<close>] Int_assoc[of _ "R\<times>R" "U\<times>U"]
        by (simp add: Times_Int_Times) fastforce
      (** U is closed because it is a bottom SCC. *)
      from new_U have \<sigma>_U_closed: "(Restr ?G\<sigma> R) `` U \<subseteq> U"
        using \<sigma>_graph.nt_bottom_SCC_closed by simp
      (** All nodes in U have a successor in U because it is nontrivial and a bottom SCC. *)
      from new_U have \<sigma>_U_succ_in_U: "\<forall>v\<in>U. \<exists>v'\<in>U. (v,v') \<in> ?G\<sigma>"
        using \<sigma>_graph.nt_bottom_SCC_succ_in_SCC by blast
      (** Now, we shot that U is a tangle for \<alpha>. *)
      show ?thesis
        unfolding tangle_iff
      proof (rule exI[where x=\<alpha>]; intro conjI)
        (** U is nonempty because it is an SCC. *)
        from new_U show "U \<noteq> {}"
          using \<sigma>_graph.nt_bottom_SCC_notempty by blast
        (** U is part of R, and R is part of V, so U is part of V. *)
        from \<open>U\<subseteq>R\<close> \<open>R\<subseteq>V\<close> show "U \<subseteq> V" by blast
        (** We will show that \<alpha> wins the top priority in U. *)
        show "player_winningP \<alpha> (pr_set U)" proof -
          (** First, we show that U and A intersect.
              U is not empty, so we can get an x in U.
              From this x, there exists a path to a node in A.
              Because U is closed in G\<sigma>, this node in A is also in U.
              Therefore, U must intersect with A. *)
          from \<open>U\<noteq>{}\<close> \<open>U\<subseteq>Z\<close> \<sigma>_path_to_A have "U \<inter> A \<noteq> {}"
            using path_closed_dest[OF _ \<sigma>_U_closed] by blast
          (** Because it contains A, which is all nodes of the highest priority in R,
              the highest priority in U is p. *)
          with \<open>U\<subseteq>R\<close> have "pr_set U = p"
            using pr_le_pr_set[OF fin_U] R_game.pr_set_le_pr_set_V[OF _ \<open>U\<noteq>{}\<close>]
            by (simp add: A_def p_def Int_absorb1[OF \<open>R\<subseteq>V\<close>]) force
          (** Since \<alpha> wins p, \<alpha> wins the highest priority in U. *)
          thus ?thesis by (simp add: \<alpha>_def player_wins_pr_def)
        qed
        (** We define a \<sigma>' that covers U. This will be our tangle strategy. *)
        define \<sigma>' where "\<sigma>' = \<sigma> |` U"
        let ?G\<sigma>' = "induced_subgraph \<sigma>'"
        have \<sigma>'_le_\<sigma>: "\<sigma>' \<subseteq>\<^sub>m \<sigma>" by (auto simp: \<sigma>'_def map_le_def)
        (** The graph of \<sigma> in U is equal to the graph of \<sigma>' in U. *)
        from restricted_strat_subgraph_same_in_region[OF \<sigma>'_def]
        have graphs_equal_in_U: "Restr ?G\<sigma> U = Restr ?G\<sigma>' U" .
        (** Therefore, all nodes in U have a successor in U. *)
        with \<sigma>_U_succ_in_U have \<sigma>'_U_succ_in_U:
          "\<forall>v\<in>U. \<exists>v'\<in>U. (v, v') \<in> ?G\<sigma>'" by blast
        (** We show that this is a tangle strategy for U. *)
        show "\<exists>\<sigma>. tangle_strat \<alpha> U \<sigma>"
          unfolding tangle_strat_iff Let_def
        proof (rule exI[where x=\<sigma>']; intro conjI)
          (** \<sigma>' is a strategy for the player. *)
          from \<sigma>_strat show \<sigma>'_strat: "strategy_of (V_player \<alpha>) \<sigma>'"
            using strat_le_E_of_strat[OF \<sigma>'_le_\<sigma>]
            by (auto simp: \<sigma>'_def strategy_of_def)
          (** The domain of \<sigma>' covers all \<alpha>-nodes in U. *)
          show \<sigma>'_dom: "dom \<sigma>' = U \<inter> V_player \<alpha>" proof
            (** The original domain of \<sigma> was a subset of \<alpha>-nodes in Z.
                \<sigma>' restricts it to U, which makes it a subset of
                \<alpha>-nodes in U. *)
            from \<sigma>_dom show "dom \<sigma>' \<subseteq> U \<inter> V_player \<alpha>"
              by (auto simp: \<sigma>'_def)
          next
            show "U \<inter> V_player \<alpha> \<subseteq> dom \<sigma>'"
            proof (rule subsetI)
              fix x assume x_in_U_\<alpha>: "x \<in> U \<inter> V_player \<alpha>"
              consider (x_in_A) "x \<in> A" | (x_notin_A) "x \<notin> A" by blast
              thus "x \<in> dom \<sigma>'" proof cases
                (** If we have a \<alpha>-node in A, it has a successor in U. *)
                case x_in_A
                from x_in_U_\<alpha> \<sigma>'_U_succ_in_U \<open>U\<subseteq>R\<close>
                have "Restr E R `` {x} \<inter> U \<noteq> {}"
                  using ind_subgraph by fast
              (** By a previous lemma, this means it is part of the domain of \<sigma>.
                  Hence, it is also part of the domain of \<sigma>'. *)
                with x_in_A x_in_U_\<alpha> \<open>U\<subseteq>Z\<close> show ?thesis
                  using R_game.tangle_attractor_strat_in_dom_A[OF fin_T attr]
                  by (auto simp: R_game_V_player_eq \<sigma>'_def)
              next
              (** If we have an \<alpha>-node outside of A, a previous lemma says
                  it is part of the domain of \<sigma>. Hence, it is also part of
                  the domain of \<sigma>'. *)
                case x_notin_A with x_in_U_\<alpha> \<open>U\<subseteq>Z\<close> \<open>U\<subseteq>R\<close> show ?thesis
                  using R_game.tangle_attractor_strat_in_dom_not_A[OF fin_T attr]
                  by (auto simp: R_game_V_player_eq \<sigma>'_def)
              qed
            qed
          qed
          (** The range of \<sigma>' lies in U because all nodes in U have a
              successor in U in the subgame of \<sigma>. *)
          from \<sigma>'_U_succ_in_U show \<sigma>'_ran: "ran \<sigma>' \<subseteq> U"
            using ran_restrictD[of _ \<sigma> U] ind_subgraph_to_strategy
            unfolding \<sigma>'_def by fastforce
          (** \<sigma> is strongly connected, so the tangle subgraph of \<sigma>' is also strongly
              connected. *)
          from \<sigma>_U_connected \<sigma>'_dom \<sigma>'_ran \<open>U\<subseteq>V\<close>
          show "strongly_connected (tangle_subgraph \<alpha> U \<sigma>') U"
            using tangle_subgraph_is_restricted_ind_subgraph
            by (simp add: graphs_equal_in_U)
          (** We show that all cycles in the tangle subgraph of U and \<sigma>' are won
              by \<alpha>. *)
          show "\<forall>v\<in>U. \<forall>xs. cycle (tangle_subgraph \<alpha> U \<sigma>') v xs \<longrightarrow> player_wins_list \<alpha> xs"
          proof -
            (** Because U is part of Z, and the graphs are the same in U,
                the tangle subgraph is part of of the subgraph of \<sigma> in Z. *)
            from \<sigma>'_dom \<sigma>'_ran \<open>U\<subseteq>Z\<close> \<open>U\<subseteq>V\<close> have tangle_subgraph_subset:
              "tangle_subgraph \<alpha> U \<sigma>' \<subseteq> Restr ?G\<sigma> Z"
              using tangle_subgraph_is_restricted_ind_subgraph
              using restricted_strat_and_dom_subgraph_same_in_region
              by (auto simp: \<sigma>'_def)
            (** This means all cycles in the tangle subgraph also exist in
                the subgraph of \<sigma> in Z. These are lassos, so they are won by \<alpha>. *)
            from in_Z_won show ?thesis
              using subgraph_path[OF tangle_subgraph_subset] subsetD[OF \<open>U\<subseteq>Z\<close>]
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

(** One step of the search algorithm preserves our invariant. *)
lemma search_step_preserves_I:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> search_I (R',Y')"
  using search_step_valid_subgame[of R Y R' Y']
  using search_step_finite_Y[of R Y R' Y']
  using search_step_tangles_Y[of R Y R' Y']
  unfolding search_I_def split by fast

(** If two states are in the reflexive transitive closure of steps, then our invariant is preserved
    between them. *)
lemma search_step_rtranclp_preserves_I:
  "\<lbrakk>search_step\<^sup>*\<^sup>* (R,Y) (R',Y'); search_I (R,Y)\<rbrakk> \<Longrightarrow> search_I (R',Y')"
  apply (induction rule: rtranclp_induct2)
  using search_step_preserves_I by blast+

(** Search preserves our invariant. *)
lemma search_preserves_I:
  "\<lbrakk>search R Y; search_I (R,{})\<rbrakk> \<Longrightarrow> search_I ({},Y)"
  using search_step_rtranclp_preserves_I
  by (simp add: search_def)


subsection \<open>Emptiness of Y'\<close>
(** When we use search, Y' can either be empty, or non-empty.
    We will show these properties in two stages.
    First, if the initial R is empty, then Y will be empty too.
    Second, if the initial R is non-empty, then Y must be non-empty. *)
subsubsection \<open>Empty Y'\<close>
(** If the initial R is empty, then there does not exists a further step. *)
lemma search_step_notempty[simp]:
  "\<not>search_step ({},Y) (R',Y')"
  by (simp add: search_step.simps)

(** If the initial R is empty, then the result of the reflexive
    transitive closure of the step must have its Y' equal to the
    initial Y. *)
lemma search_step_rtranclp_empty_R:
  "search_step\<^sup>*\<^sup>* ({},Y) (R',Y') \<Longrightarrow> Y' = Y"
proof -
  assume step: "search_step\<^sup>*\<^sup>* ({},Y) (R',Y')"
  (** By the previous lemma, no steps can be taken, so our induction
      shows that the only step in the reflexive transitive closure
      is the reflexive case. This shows our thesis is true. *)
  have "\<lbrakk>search_step\<^sup>*\<^sup>* (R,Y) (R',Y'); R = {}\<rbrakk> \<Longrightarrow> Y' = Y" for R
    by (induction rule: converse_rtranclp_induct2) auto
  from this[OF step] show ?thesis by simp
qed

(** Search does not find any tangles in an empty region. *)
lemma search_empty_R:
  "search {} Y \<Longrightarrow> Y = {}"
  using search_step_rtranclp_empty_R
  unfolding search_def by blast


subsubsection \<open>Nonempty Y'\<close>
(** When we reach the final step, where R' is empty, Y' must be nonempty. *)
lemma search_step_last_Y'_nonempty:
  "\<lbrakk>search_step (R,Y) (R',Y'); search_I (R,Y); R' = {}\<rbrakk> \<Longrightarrow> Y' \<noteq> {}"
  unfolding search_I_def split
proof (induction rule: search_step_induct)
  case (step R p \<alpha> A Z \<sigma> Ov Y' Y R')
  (** From the step, we know R is a valid parity game. *)
  then interpret R_game:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R" by blast
  (** We also know that Z is an attractor, and R is part of V and equal to Z. *)
  from step have attr: "R_game.tangle_attractor \<alpha> T A Z \<sigma>" by simp
  from step have "R \<subseteq> V" by blast
  from step have "R = Z"
    using R_game.tangle_attractor_in_V[OF fin_T attr] by blast
  (** Shorthand for the subgame of \<sigma> and its nodes. *)
  let ?G\<sigma> = "induced_subgraph \<sigma>"
  let ?V\<sigma> = "induced_subgraph_V \<sigma>"
  (** Because Z is a tangle attractor, \<sigma> is a strategy for \<alpha> in R, and the range
      of \<sigma> lies in R. *)
  from \<open>R=Z\<close> R_game.tangle_attractor_strat[OF fin_T attr] have
    \<sigma>_strat_R: "R_game.strategy_of_player \<alpha> \<sigma>" and
    \<sigma>_ran: "ran \<sigma> \<subseteq> R" by auto
  (** The subgame of \<sigma> is the same in R in the whole game as it is in
      R in the subgame R. *)
  with restr_ind_subgraph_V[OF R_game.arena_axioms _ _ \<open>R\<subseteq>V\<close>]
  have R_game_V\<sigma>_eq: "R_game.induced_subgraph_V \<sigma> = ?V\<sigma> \<inter> R"
    using restr_subgraph_strat_of_player[OF R_game.paritygame_axioms]
    by blast
  have R_game_G\<sigma>_eq:
    "R_game.induced_subgraph \<sigma> = Restr ?G\<sigma> R"
    using restr_ind_subgraph[OF R_game.arena_axioms] .
  (** Now, we can show that the subgraph of \<sigma> in R is a finite
      graph without dead ends. *)
  from \<sigma>_strat_R interpret \<sigma>_graph_R:
    finite_graph_V_succ "Restr ?G\<sigma> R" "?V\<sigma> \<inter> R"
    unfolding induced_subgraph_V_def
    apply (unfold_locales; force?)
    subgoal for v using R_game.ind_subgraph_succ[of v]
      using R_game_G\<sigma>_eq R_game_V\<sigma>_eq induced_subgraph_V_def
      unfolding R_game.strategy_of_player_def R_game.strategy_of_def
      by clarsimp blast
    done
  (** There are no open vertices because every node has a successor in Z. *)
  from \<open>R=Z\<close> step have "Ov = {}"
    using R_game.succ by auto
  with step have "Y' = Y \<union> {U. bound_nt_bottom_SCC R Z \<sigma> U}"
    by presburger
  (** We show there exists a nontrivial bottom SCC in Z. *)
  moreover have "\<exists>U. bound_nt_bottom_SCC R Z \<sigma> U"
  proof -
    (** The subgraph of \<sigma> in R has nodes in it. *)
    from \<sigma>_strat_R \<open>R\<subseteq>V\<close> \<open>R\<noteq>{}\<close> have "?V\<sigma> \<inter> R \<noteq> {}"
      unfolding R_game.strategy_of_player_def
      using R_game.strategy_of_in_E[of _ \<sigma>]
      using R_game.ind_subgraph_V_notempty[of \<sigma>]
      using R_game_V\<sigma>_eq by blast
    (** This means there exists a nontrivial bottom SCC. *)
    with \<open>R=Z\<close> show ?thesis
      using \<sigma>_graph_R.nt_bottom_SCC_ex
      using \<sigma>_graph_R.nt_bottom_SCC_in_V by blast
  qed
  ultimately show ?case by simp
qed

(** If the initial R is nonempty, and the resulting R' of the reflexive
    transitive closure of search_step is empty, then the obtained Y' is not empty. *)
lemma search_step_rtranclp_last_Y'_nonempty:
  "\<lbrakk>search_step\<^sup>*\<^sup>* (R,Y) (R',Y'); search_I (R,Y); R \<noteq> {}; R' = {}\<rbrakk> \<Longrightarrow> Y' \<noteq> {}"
  apply (induction rule: rtranclp_induct2)
  by (auto simp: search_step_last_Y'_nonempty search_step_rtranclp_preserves_I)

(** If we have a nonempty R that is a valid subgame, then search gives a nonempty Y. *)
lemma search_nonempty_R:
  "\<lbrakk>search R Y; valid_subgame R; R \<noteq> {}\<rbrakk> \<Longrightarrow> Y \<noteq> {}"
  using search_step_rtranclp_last_Y'_nonempty search_I_base
  unfolding search_def by simp

(** If the initial R is a valid subgame, then Y will be nonempty so long as R is nonempty. *)
lemma search_Y_notempty_iff_R_notempty:
  "\<lbrakk>search R Y; valid_subgame R\<rbrakk> \<Longrightarrow> R \<noteq> {} \<longleftrightarrow> Y \<noteq> {}"
  using search_empty_R search_nonempty_R by blast

subsection \<open>Correctness\<close>
(** If the initial R is a valid subgame, then search gives us a finite, non-empty Y that contains
    new tangles that were not included in T before. *)
theorem search_correct:
  "\<lbrakk>valid_subgame R; search R Y\<rbrakk>
    \<Longrightarrow> finite Y \<and> (R \<noteq> {} \<longleftrightarrow> Y \<noteq> {}) \<and> (\<forall>U \<in> Y. \<exists>\<alpha>. tangle \<alpha> U)"
  using search_I_correct[OF search_preserves_I[OF _ search_I_base]]
  using search_Y_notempty_iff_R_notempty by simp


section \<open>Termination\<close>
(** R is strictly decreasing at every step of search. *)
lemma search_step_R_decreasing:
  "\<lbrakk>search_step (R,Y) (R',Y'); valid_subgame R\<rbrakk> \<Longrightarrow> R' \<subset> R"
  apply (induction rule: search_step_induct)
  subgoal for R
    using pr_set_exists[OF finite_subset[OF _ fin_V, of R]]
    using paritygame.target_in_tangle_attractor[OF _ fin_T]
    by blast
  done

(** If our invariant holds at every step, then our step relation
    is well-founded. *)
lemma search_step_wfP_I:
  "wfP (\<lambda>s' s. search_step s s' \<and> search_I s)"
  unfolding wfP_def
  apply (rule wf_subset[of "inv_image finite_psubset (\<lambda>(R,Y). R)"])
  using search_step_R_decreasing by (auto simp: search_I_def finite_subset)

(** Since the invariant holds initially, and it is preserved
    at each step, search_step terminates for the initial state
    (R,{}). *)
theorem search_step_terminates:
  assumes "valid_subgame R"
  shows "trm search_step (R,{})"
  apply (rule wfP_I_terminates[where I=search_I])
  using search_I_base[OF assms]
  using search_step_preserves_I
  using search_step_wfP_I
  unfolding search_I_def split by blast+

(** If our invariant holds for a state (R,Y), but no further steps can be
    taken from it, then R is empty. *)
lemma search_step_final_empty_R:
  assumes I: "search_I (R,Y)"
  assumes final: "\<not>Domainp search_step (R,Y)"
  shows "R = {}"
proof (rule ccontr)
  assume "R \<noteq> {}"
  (** By the invariant, R is a balid subgame. *)
  from I interpret subgame:
    paritygame "Restr E R" "V\<inter>R" "V\<^sub>0\<inter>R"
    unfolding search_I_def split by blast
  (** Because R is not empty, another step can be taken. *)
  from \<open>R\<noteq>{}\<close> obtain R' Y' where
    "search_step (R,Y) (R',Y')"
    using subgame.tangle_attractor_exists[OF fin_T]
    using search_step.step[of R _ _ _ _ _ _ _ Y]
    by clarsimp fastforce
  (** This means the state (R,Y) lies in the domain of the
      step, which is a contradiction with our assumptions. *)
  hence "Domainp search_step (R,Y)" by blast
  with final show False by blast
qed

(** Because our step terminates, and because the final step
    always has an empty R, there always exists a resulting Y
    for any initial R. *)
theorem search_result_exists:
  assumes "valid_subgame R"
  shows "\<exists>Y. search R Y"
  using search_I_base[OF assms]
  using trm_final_state[OF search_step_terminates[OF assms]]
  using search_step_final_empty_R[OF search_step_rtranclp_preserves_I]
  unfolding search_def by fast
end (** End of context with fixed T. *)
end (** End of context paritygame. *)

end
