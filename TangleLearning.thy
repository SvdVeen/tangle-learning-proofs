theory TangleLearning
imports Main ParityGames
begin
chapter \<open>Tangle Learning\<close>
section \<open>Tangle Definitions\<close>

context paritygame begin

  (** As defined by Van Dijk:
      A p-tangle is a nonempty set of vertices U \<subseteq> V with p = pr(U),
      for which player \<alpha> \<equiv>\<^sub>2 p has a strategy \<sigma>: U\<^sub>\<alpha> \<rightarrow> U, such that the graph (U,E'),
      with E' := E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)), is strongly connected and player \<alpha> wins all cycles in (U,E').*)
  definition p_tangle :: "nat \<Rightarrow> 'v set \<Rightarrow> bool" where
    "p_tangle p U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> p = Max (pr ` U) \<and>
    (let \<alpha> = player_wins_pr p in (
      \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
      (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
        strongly_connected E' \<and>
        (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
    ))))"

  definition tangle_strat :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "tangle_strat U \<sigma> \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and>
   (let \<alpha> = player_wins_pr (pr_set U) in (
      strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
        (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
          strongly_connected E' \<and>
          (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
   ))))"

  lemma tangle_strat_notempty[simp]: "\<not>tangle_strat {} \<sigma>"
    unfolding tangle_strat_def by simp

  lemma tangle_strat_in_V: "tangle_strat U \<sigma> \<Longrightarrow> U \<subseteq> V"
    unfolding tangle_strat_def by simp

  definition tangle' :: "'v set \<Rightarrow> bool" where
    "tangle' U \<equiv> \<exists>\<sigma>. tangle_strat U \<sigma>"

  lemma tangle'_notempty[simp]: "\<not>tangle' {}"
    unfolding tangle'_def by simp

  definition tangle :: "'v set \<Rightarrow> bool" where
    "tangle U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and>
    (let \<alpha> = player_wins_pr (pr_set U) in (
      \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
      (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
        strongly_connected E' \<and>
        (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
    ))))"

  lemma tangle_notempty[simp]: "\<not>tangle {}"
    unfolding tangle_def by simp

  lemma tangle_in_V: "tangle U \<Longrightarrow> U \<subseteq> V"
    unfolding tangle_def by simp

  lemma closed_tangle_is_winning_region:
    assumes tangle: "tangle U"
    assumes closed_opp: "\<forall>u \<in> U. u \<in> V_opponent (player_wins_pr(pr_set U)) \<longrightarrow> E `` {u} \<subseteq> U"
    shows "winning_region (player_wins_pr (pr_set U)) U"
  proof -
    from tangle have U_in_V: "U \<subseteq> V" using tangle_in_V by simp

    let ?\<alpha> = "player_wins_pr (pr_set U)"
    from tangle obtain \<sigma> where
        \<sigma>_strat: "strategy_of_player ?\<alpha> \<sigma>"
    and \<sigma>_dom: "dom \<sigma> = U \<inter> V_player ?\<alpha>"
    and \<sigma>_ran: "ran \<sigma> \<subseteq> U"
    and \<sigma>_conn: "strongly_connected (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
    and \<sigma>_winning: "\<forall>v\<in>U. \<forall>xs. cycle_node (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U)) v xs
      \<longrightarrow> player_wins_list ?\<alpha> xs"
      unfolding tangle_def Let_def by auto

    from \<sigma>_dom closed_opp have \<sigma>_subgraph_closed: "induced_subgraph (dom \<sigma>) \<sigma> `` U \<subseteq> U"
      using ind_subgraph_closed_region[OF U_in_V _ \<sigma>_ran, of "dom \<sigma>"]
      using V_opponent_player_int[OF U_in_V, of ?\<alpha>]
      by blast

    have \<sigma>_winning': "\<forall>u\<in>U. \<forall>ys. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) u ys
          \<longrightarrow> player_wins_list (player_wins_pr (pr_set U)) ys"
    proof (rule ballI; rule allI; rule impI)
      fix u ys
      assume u_in_U: "u \<in> U" and cycle_u_ys: "cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) u ys"
      from cycle_from_node_closed_set[OF u_in_U \<sigma>_subgraph_closed cycle_u_ys]
      have ys_in_U: "set ys \<subseteq> U" .

        from cycle_u_ys ys_in_U obtain y where
            cycle_y_ys: "cycle_node (induced_subgraph (dom \<sigma>) \<sigma>) y ys"
        and y_in_U: "y \<in> U"
          unfolding cycle_from_node_def
          using origin_in_cycle_node by fastforce

        have "induced_subgraph (dom \<sigma>) \<sigma> \<inter> (U\<times>U) \<subseteq> (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
          apply (subst \<sigma>_dom; simp; rule conjI)
          subgoal using ind_subgraph[of "U \<inter> V_player ?\<alpha>"] by blast
          subgoal apply (subst V_opponent_player_int[OF U_in_V])
            unfolding induced_subgraph_def by fast
          done
        from \<sigma>_winning y_in_U subgraph_cycle[OF this cycle_restr_V[OF cycle_y_ys ys_in_U]]
        show "player_wins_list ?\<alpha> ys" by simp
    qed

    show "winning_region ?\<alpha> U"
      apply (simp add: winning_region_strat tangle_in_V[OF tangle])
      apply (rule exI[where x="\<sigma>"]; intro conjI)
      subgoal using \<sigma>_strat .
      subgoal using \<sigma>_dom Int_commute ..
      subgoal using \<sigma>_ran .
      subgoal using \<sigma>_winning' .
      subgoal using closed_opp .
      done
  qed

  definition player_tangle :: "player \<Rightarrow> 'v set \<Rightarrow> bool" where
    "player_tangle \<alpha> U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> \<alpha> = player_wins_pr (pr_set U) \<and>
    (\<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
    (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
      strongly_connected E' \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
    )))"

  lemma player_tangle_notempty[simp]: "\<not>player_tangle \<alpha> {}"
    unfolding player_tangle_def by simp

  lemma player_tangle_in_V: "player_tangle \<alpha> U \<Longrightarrow> U \<subseteq> V"
    unfolding player_tangle_def by simp

  lemma player_tangle_equiv_tangle: "tangle U \<longleftrightarrow> player_tangle (player_wins_pr (pr_set U)) U"
    unfolding tangle_def player_tangle_def Let_def by simp

  (** lemma ind_subgraph_int: "\<lbrakk>dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> U; ran \<sigma> \<subseteq> U\<rbrakk>
    \<Longrightarrow> E \<inter> (((U-V\<^sub>\<alpha>) \<times> U) \<union> E_of_strat \<sigma>) = induced_subgraph (U \<inter> V\<^sub>\<alpha>) \<sigma> \<inter> (U\<times>U)"
    apply (subst ind_subgraph_in_V)
    apply safe
    subgoal using E_in_V by blast
    subgoal using E_in_V by blast
    subgoal unfolding E_of_strat_def by blast
    subgoal unfolding E_of_strat_def using ranI by fast
    done *)
end

context player_paritygame
begin
  definition player_tangle' :: "'v set \<Rightarrow> bool" where
    "player_tangle' U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> winningP (pr_set U) \<and>
    (\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V\<^sub>\<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
    (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V\<^sub>\<beta>) \<times> U) in (
      strongly_connected E' \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> winning_player xs)
    )))"

  lemma player_tangle'_notempty[simp]: "\<not>player_tangle' {}"
    unfolding player_tangle'_def by simp

  lemma player_tangle'_in_V: "player_tangle' U \<Longrightarrow> U \<subseteq> V"
    unfolding player_tangle'_def by simp
end

context paritygame
begin
  lemma player_tangles_equiv: "player_tangle \<alpha> = (if \<alpha> = EVEN then P0.player_tangle' else P1.player_tangle')"
    unfolding player_tangle_def P0.player_tangle'_def P1.player_tangle'_def Let_def
    unfolding player_wins_pr_def strategy_of_player_def
    using V\<^sub>1_def V_diff_diff_V\<^sub>0 by (cases \<alpha>) auto
end

context player_paritygame
begin

  definition opponent_escapes :: "'v set \<Rightarrow> 'v set" where
    "opponent_escapes t \<equiv> {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V\<^sub>\<beta> \<and> v \<in> V - t}"

  lemma opponent_escapes_in_V: "opponent_escapes t \<subseteq> V"
    unfolding opponent_escapes_def by auto

  lemma fin_opponent_escapes: "finite (opponent_escapes t)"
    using finite_subset[OF opponent_escapes_in_V fin_V] .

  lemma player_tangle'_escapes: "player_tangle' U
    \<Longrightarrow> (\<forall>v\<in>U \<inter> V\<^sub>\<beta>. \<forall>w. (v,w) \<in> E \<longrightarrow> w \<in> U \<or> w \<in> opponent_escapes U)"
    unfolding opponent_escapes_def
    using E_in_V by auto

context
  fixes T :: "'v set set"
  assumes tangles_T : "\<forall>t\<in>T. player_tangle' t"
  assumes finite_T: "finite T"
begin

  inductive_set player_tangle_attractor :: "'v set \<Rightarrow> 'v set" for A where
    base: "x \<in> A \<Longrightarrow> x \<in> player_tangle_attractor A"
  | own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-A; (x,y) \<in> E; y \<in> player_tangle_attractor A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor A"
  | opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-A; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> player_tangle_attractor A\<rbrakk>
                \<Longrightarrow> x \<in> player_tangle_attractor A"
  | escape: "\<lbrakk>x \<in> t-A; t \<in> T; opponent_escapes t \<noteq> {};
              \<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> player_tangle_attractor A\<rbrakk>
              \<Longrightarrow> x \<in> player_tangle_attractor A"

  lemma player_tangle_attractor_subset[simp]: "A \<subseteq> player_tangle_attractor A"
    by (auto intro: player_tangle_attractor.base)

  definition \<alpha>_maximal :: "'v set \<Rightarrow> bool" where
    "\<alpha>_maximal A \<equiv> A = player_tangle_attractor A"

    context
      fixes A :: "'v set"
    begin
      fun tangle_nodes_in_rank :: "nat \<Rightarrow> 'v set" where
        "tangle_nodes_in_rank 0 = A"
      | "tangle_nodes_in_rank (Suc n) =
         tangle_nodes_in_rank n
         \<union> { x | x y :: 'v. x\<in>V\<^sub>\<alpha> \<and> (x,y)\<in>E \<and> y\<in>tangle_nodes_in_rank n }
         \<union> { x. x\<in>V\<^sub>\<beta> \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>tangle_nodes_in_rank n) }
         \<union> { x | x t. x\<in>t - A  \<and> t\<in>T \<and> opponent_escapes t \<noteq> {} \<and>
            (\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v\<in>tangle_nodes_in_rank n)}"

      lemma tangle_nodes_in_rank_Suc_cases:
        assumes "x \<in> tangle_nodes_in_rank (Suc n)"
        obtains (base) "x \<in> tangle_nodes_in_rank n"
        | (own) "x \<in> V\<^sub>\<alpha> \<and> (\<exists>y. (x,y)\<in>E \<and> y \<in> tangle_nodes_in_rank n)"
        | (opponent) "x \<in> V\<^sub>\<beta> \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>tangle_nodes_in_rank n)"
        | (escape) "\<exists>t. x \<in> t - A \<and> t \<in> T \<and> opponent_escapes t \<noteq> {} \<and>
                    (\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> tangle_nodes_in_rank n)"
        using assms by force

      lemma tangle_nodes_in_rank_mono: "n\<le>m \<Longrightarrow> tangle_nodes_in_rank n \<subseteq> tangle_nodes_in_rank m"
        using le_Suc_eq by (induction m) auto

      lemma tangle_nodes_in_rank_subset: "A \<subseteq> tangle_nodes_in_rank n"
        using tangle_nodes_in_rank.simps(1) tangle_nodes_in_rank_mono by blast

      lemma tangle_nodes_in_rank_ss_player_tangle_attractor:
        "tangle_nodes_in_rank n \<subseteq> player_tangle_attractor A"
        apply (induction n; rule)
        subgoal using tangle_nodes_in_rank_subset player_tangle_attractor_subset by fastforce
        subgoal for n x apply (cases rule: tangle_nodes_in_rank_Suc_cases; simp)
          subgoal by fast
          subgoal by (auto intro: player_tangle_attractor.intros)
          subgoal by (auto intro: player_tangle_attractor.intros)
          subgoal using player_tangle_attractor.escape DiffI subset_iff by metis
          done
        done

      lemma player_tangle_attractor_ss_tangle_nodes_in_rank:
        "x\<in>player_tangle_attractor A \<Longrightarrow> (\<exists>n. x\<in>tangle_nodes_in_rank n)"
      proof (induction rule: player_tangle_attractor.induct)
        case (base x) thus ?case using tangle_nodes_in_rank.simps(1) by blast
      next
        case (own x y) thus ?case using tangle_nodes_in_rank.simps(2) by fast
      next
        case (opponent x)
        define n_of_y where "n_of_y \<equiv> \<lambda>y. SOME n. y \<in> tangle_nodes_in_rank n"
        define n_max where "n_max \<equiv> MAX y\<in>E``{x}. n_of_y y"
        have FIN: "finite (n_of_y ` E `` {x})" by auto

        have n_of_y: "(x,y)\<in>E \<Longrightarrow> y\<in>tangle_nodes_in_rank (n_of_y y)" for y
          unfolding n_of_y_def using opponent.IH by (auto intro: someI)

        have "(x,y)\<in>E \<Longrightarrow> (\<exists>i\<le>n_max. y\<in>tangle_nodes_in_rank i)" for y
          using Max_ge[OF FIN] n_of_y unfolding n_max_def by blast
        hence "(x,y)\<in>E \<Longrightarrow> y\<in>tangle_nodes_in_rank n_max" for y
          using tangle_nodes_in_rank_mono by auto
        thus ?case
          apply (rule_tac exI[where x="Suc n_max"])
          using opponent.hyps by simp
      next
        case (escape x t)
        define n_of_y where "n_of_y \<equiv> \<lambda>y. SOME n. y \<in> tangle_nodes_in_rank n"
        define n_max where "n_max \<equiv> MAX y \<in> opponent_escapes t. n_of_y y"
        have FIN: "finite (n_of_y ` opponent_escapes t)"
          using fin_opponent_escapes by fast

        have n_of_y: "y \<in> opponent_escapes t \<Longrightarrow> y \<in> tangle_nodes_in_rank (n_of_y y)" for y
          unfolding n_of_y_def using escape.IH by (auto intro: someI)

        have "y \<in> opponent_escapes t \<Longrightarrow> (\<exists>i\<le>n_max. y \<in> tangle_nodes_in_rank i)" for y
          using Max_ge[OF FIN] n_of_y unfolding n_max_def by blast
        hence "y \<in> opponent_escapes t \<Longrightarrow> y \<in> tangle_nodes_in_rank n_max" for y
          using tangle_nodes_in_rank_mono by auto
        thus ?case
          apply (rule_tac exI[where x="Suc n_max"])
          using escape.hyps by auto
      qed

      lemma player_tangle_attractor_eq_tangle_nodes_in_rank:
        "player_tangle_attractor A = \<Union>(tangle_nodes_in_rank`UNIV)"
        using player_tangle_attractor_ss_tangle_nodes_in_rank
        using tangle_nodes_in_rank_ss_player_tangle_attractor
        by fast

      lemma tangle_nodes_in_rank_edges_same: "\<lbrakk>x\<in>tangle_nodes_in_rank n; x\<notin>A; (x,y)\<in>E; x\<notin>V\<^sub>\<alpha>\<rbrakk>
        \<Longrightarrow> y\<in>tangle_nodes_in_rank n"
      proof (induction n)
        case 0 thus ?case by simp
      next
        case (Suc n)
        from Suc(2) show ?case proof (cases rule: tangle_nodes_in_rank_Suc_cases)
          case base
          from Suc.IH[OF base Suc.prems(2,3,4)] show ?thesis by simp
        next
          case own with Suc.prems(4) show ?thesis by blast
        next
          case opponent with Suc.prems(3) show ?thesis by auto
        next
          case escape
          then obtain t where
              x_in_t: "x \<in> t - A"
          and t_in_T: "t \<in> T"
          and t_has_escapes: "opponent_escapes t \<noteq> {}"
          and escapes_in_n: "\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> tangle_nodes_in_rank n"
            by blast

          from t_in_T have t_tangle: "player_tangle' t" using tangles_T by fast

          from Suc.prems(3,4) have "x \<in> V\<^sub>\<beta>" using E_in_V by blast
          with x_in_t have x_in_V\<^sub>\<beta>_U_t: "x \<in> V\<^sub>\<beta> \<inter> (t - A)" by blast
          with t_tangle Suc.prems(3) have "y \<in> t \<or> y \<in> opponent_escapes t"
            using player_tangle'_escapes by blast

          with t_in_T t_has_escapes escapes_in_n show ?thesis
            using tangle_nodes_in_rank_subset apply simp by blast
        qed
      qed

      fun construct_strat :: "'v strat \<Rightarrow> 'v strat list \<Rightarrow> 'v strat" where
        "construct_strat \<sigma> [] = \<sigma>"
      | "construct_strat \<sigma> (\<sigma>'#xs) = construct_strat (\<sigma> ++ (\<sigma>' |` (- dom \<sigma>))) xs"

      lemma construct_strat_dom_empty[simp]: "dom (construct_strat \<sigma> []) = dom \<sigma>"
        by simp

      lemma construct_strat_ran_empty[simp]: "ran (construct_strat \<sigma> []) = ran \<sigma>"
        by simp

      lemma construct_strat_dom: "dom (construct_strat \<sigma> xs) = dom \<sigma> \<union> \<Union>(dom ` set xs)"
        apply (induction xs arbitrary: \<sigma>; simp) by blast

      lemma construct_strat_retain_dom: "dom \<sigma> \<subseteq> dom (construct_strat \<sigma> xs)"
        using construct_strat_dom by auto

      lemma construct_strat_retain_ran: "ran \<sigma> \<subseteq> ran (construct_strat \<sigma> xs)"
        apply (rule subsetI)
        by (induction xs arbitrary: \<sigma>; simp add: ran_map_add)

      lemma construct_strat_retain_strat: "\<sigma> \<subseteq>\<^sub>m construct_strat \<sigma> xs"
        apply (induction xs arbitrary: \<sigma>; simp)
        unfolding map_le_def by (simp add: map_add_dom_app_simps(3))

      lemma construct_strat_retain_strat': "x \<in> dom \<sigma> \<Longrightarrow> (construct_strat \<sigma> xs) x = \<sigma> x"
        using construct_strat_retain_strat unfolding map_le_def by simp

      lemma "\<lbrakk>ran \<sigma> \<subseteq> R; \<forall>\<sigma>' \<in> set xs. ran \<sigma>' \<subseteq> R\<rbrakk> \<Longrightarrow> ran (construct_strat \<sigma> xs) \<subseteq> R"
      proof (induction xs arbitrary: \<sigma>)
        case Nil thus ?case by fastforce
      next
        case (Cons a xs)
        from Cons.prems(2) have a_ran: "ran a \<subseteq> R" by simp
        from Cons.prems(2) have xs_ran: "\<forall>\<sigma>'\<in>set xs. ran \<sigma>' \<subseteq> R" by simp
        from Cons show ?case sorry
      qed

lemma combined_tangle_strat:
  assumes fin_S: "finite S"
  assumes tangles_S: "\<forall>t\<in>S. player_tangle' t"
  shows "\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
             dom \<sigma> = \<Union>S \<inter> V\<^sub>\<alpha> \<and>
             ran \<sigma> \<subseteq> \<Union>S"
proof -
  define tangle_strat where "tangle_strat = (\<lambda>t \<sigma>.
    strategy_of V\<^sub>\<alpha> \<sigma> \<and>
    dom \<sigma> = t \<inter> V\<^sub>\<alpha> \<and>
    ran \<sigma> \<subseteq> t \<and>
    strongly_connected (E \<inter> (E_of_strat \<sigma> \<union> (t \<inter> (V - V\<^sub>\<alpha>)) \<times> t)) \<and>
    (\<forall>v\<in>t. \<forall>xs. cycle_node (E \<inter> (E_of_strat \<sigma> \<union> (t \<inter> (V - V\<^sub>\<alpha>)) \<times> t)) v xs
       \<longrightarrow> winning_player xs))"

  define t_target where "t_target = (\<lambda>t. SOME \<sigma>. tangle_strat t \<sigma>)"

  {
    fix t
    assume "t\<in>S"
    with tangles_S have \<sigma>_exI: "\<exists>\<sigma>. tangle_strat t \<sigma>"
      unfolding player_tangle'_def Let_def tangle_strat_def by fast
    have "tangle_strat t (t_target t)"
      using someI_ex[OF \<sigma>_exI]
      unfolding t_target_def .
  } note S_target=this

  define S_strats where "S_strats = t_target ` S"

  have S_strats_all_S: "\<forall>t\<in>S. \<exists>\<sigma>\<in>S_strats. tangle_strat t \<sigma>"
    unfolding S_strats_def
    using S_target by fast

  have S_all_S_strats: "\<forall>\<sigma>\<in>S_strats. \<exists>t\<in>S. tangle_strat t \<sigma>"
    unfolding S_strats_def
    using S_target by fast

  have S_empty_iff_strats_empty: "S = {} \<longleftrightarrow> S_strats = {}"
    unfolding S_strats_def by simp

  obtain xs where xs_set_strats: "set xs = S_strats"
    unfolding S_strats_def
    using finite_list[OF finite_imageI[OF fin_S, of "t_target"]] by blast

  have strats_empty_iff_xs_empty: "S_strats = {} \<longleftrightarrow> xs = []"
    using xs_set_strats by auto

  have S_empty_iff_xs_empty: "S = {} \<longleftrightarrow> xs = []"
    by (simp add: S_empty_iff_strats_empty strats_empty_iff_xs_empty)

  define combine_strats where
    "combine_strats = (\<lambda>xs::'v strat list. fold (\<lambda>\<sigma> \<sigma>'. \<sigma> ++ (\<sigma>' |` (-dom \<sigma>))) xs Map.empty)"

  define \<sigma> where "\<sigma> = fold (\<lambda>\<sigma> \<sigma>'. \<sigma> ++ (\<sigma>' |` (-dom \<sigma>))) xs Map.empty"

  find_theorems fold
  have \<sigma>_dom: "dom \<sigma> = \<Union>S \<inter> V\<^sub>\<alpha>"
  proof (cases xs)
    case Nil with S_empty_iff_xs_empty show ?thesis
      unfolding \<sigma>_def by simp
  next
    case (Cons a list)
    then show ?thesis
      unfolding \<sigma>_def sorry
  qed

  show ?thesis
    apply (rule exI[where x="\<sigma>"])
    sorry
qed

      (** There are two possibilities with tangle attractors: either they force a play to A,
          or the player wins the play because it stays in a tangle for that player.
          This needs work: a path could start anywhere in a tangle t and take several steps before
          leaving, meaning that the path could reach A in more than n steps. *)
      lemma tangle_nodes_in_rank_strat: "\<exists>\<sigma>.
        strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (tangle_nodes_in_rank n - A) \<and> ran \<sigma> \<subseteq> tangle_nodes_in_rank n
        \<and> (\<forall>m. \<forall>x \<in> tangle_nodes_in_rank m - A. (\<forall>y \<in> (induced_subgraph V\<^sub>\<alpha> \<sigma>) `` {x}. y \<in> tangle_nodes_in_rank m))
        \<and> (\<forall>x \<in> tangle_nodes_in_rank n. \<forall>xs z. path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs z \<and> n < length xs
           \<longrightarrow> (set xs \<inter> A \<noteq> {} \<or> winning_player xs))"
      proof (induction n)
        case 0 thus ?case
          apply (rule exI[where x="Map.empty"])
          apply (intro conjI; simp)
          subgoal using tangle_nodes_in_rank_edges_same by blast
          subgoal using origin_in_path by fast
          done
      next
        case (Suc n)
        from Suc.IH obtain \<sigma> where
            \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>"
        and \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (tangle_nodes_in_rank n - A)"
        and \<sigma>_ran: "ran \<sigma> \<subseteq> tangle_nodes_in_rank n"
        and \<sigma>_closed_rank: "\<forall>m. \<forall>x\<in>tangle_nodes_in_rank m - A. \<forall>y\<in>induced_subgraph V\<^sub>\<alpha> \<sigma> `` {x}. y \<in> tangle_nodes_in_rank m"
        and \<sigma>_forces_A_or_wins: "\<forall>x \<in> tangle_nodes_in_rank n. \<forall>xs z. path (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs z \<and> n < length xs
                                 \<longrightarrow> set xs \<inter> A \<noteq> {} \<or> winning_player xs"
          by auto

        let ?all_new_player_nodes = "(tangle_nodes_in_rank (Suc n) - tangle_nodes_in_rank n) \<inter> V\<^sub>\<alpha>"
        define new_player_nodes_no_tangle where "new_player_nodes_no_tangle = ?all_new_player_nodes - \<Union>T"
        define new_player_nodes_tangle where "new_player_nodes_tangle = ?all_new_player_nodes \<inter> \<Union>T"

        have new_player_nodes_disjoint: "new_player_nodes_no_tangle \<inter> new_player_nodes_tangle = {}"
          unfolding new_player_nodes_no_tangle_def new_player_nodes_tangle_def by blast

        define tangle_strat where "tangle_strat = (\<lambda>t \<sigma>.
          strategy_of V\<^sub>\<alpha> \<sigma> \<and>
          dom \<sigma> = t \<inter> V\<^sub>\<alpha> \<and>
          ran \<sigma> \<subseteq> t \<and>
          strongly_connected (E \<inter> (E_of_strat \<sigma> \<union> (t \<inter> (V - V\<^sub>\<alpha>)) \<times> t)) \<and>
          (\<forall>v\<in>t. \<forall>xs. cycle_node (E \<inter> (E_of_strat \<sigma> \<union> (t \<inter> (V - V\<^sub>\<alpha>)) \<times> t)) v xs
             \<longrightarrow> winning_player xs))"

        define new_tangles where "new_tangles = {t. t\<in>T \<and> t \<inter> new_player_nodes_tangle \<noteq> {}}"
        have new_tangles_tangles: "\<forall>t\<in>new_tangles. player_tangle' t"
          unfolding new_tangles_def
          using tangles_T by fast
        have finite_new_tangles: "finite new_tangles"
          unfolding new_tangles_def using finite_T by force
        hence new_tangles_strats: "\<forall>t \<in> new_tangles. \<exists>\<sigma>. tangle_strat t \<sigma>"
          unfolding new_tangles_def player_tangle'_def Let_def tangle_strat_def by blast

        define t_strat where "t_strat = (\<lambda>t. SOME \<sigma>. tangle_strat t \<sigma>)"
        {
          fix t
          assume "t \<in> new_tangles"
          hence exI_\<sigma>: "\<exists>\<sigma>. tangle_strat t \<sigma>"
            using new_tangles_strats by simp
          hence "tangle_strat t (t_strat t)"
            unfolding t_strat_def
            using someI_ex[of "tangle_strat t"] by fast
        } note t_strat=this

        define new_tangle_strats where "new_tangle_strats = t_strat ` new_tangles"
        have finite_new_tangle_strats: "finite new_tangle_strats"
          unfolding new_tangle_strats_def
          using finite_new_tangles by simp
        then obtain xs where xs_is_tangle_strats: "set xs = new_tangle_strats"
          using finite_list by auto

        define target where "target = (\<lambda>x. SOME x'. x'\<in>tangle_nodes_in_rank n \<and> (x,x')\<in>E)"

        {
          fix x
          assume "x\<in>new_player_nodes_no_tangle"
          hence "target x\<in>tangle_nodes_in_rank n" "(x,target x)\<in>E"
            unfolding new_player_nodes_no_tangle_def
            apply simp_all
            using some_eq_imp[of _ "target x"]
            unfolding target_def by blast+
        } note target=this

        have target_eq: "x\<in>new_player_nodes_no_tangle \<longleftrightarrow>
          (x\<in>tangle_nodes_in_rank (Suc n) \<and> x\<in>V\<^sub>\<alpha> - \<Union>T \<and> x\<notin>tangle_nodes_in_rank n \<and>
           target x\<in>tangle_nodes_in_rank n \<and> (x,target x)\<in>E)" for x
          unfolding new_player_nodes_no_tangle_def
          apply (rule iffI; simp)
          using some_eq_imp[of _ "target x"]
          unfolding target_def by blast+

        show ?case sorry
      qed
    end
  end
end

end