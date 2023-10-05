theory TangleLearning
imports Main ParityGames
begin
chapter \<open>Tangle Learning\<close>

(** Van Dijk defines a tangle as follows:
      A p-tangle is a nonempty set of vertices U \<subseteq> V with p = pr(U),
      for which player \<alpha> \<equiv>\<^sub>2 p has a strategy \<sigma>: U\<^sub>\<alpha> \<rightarrow> U, such that the graph (U,E'),
      with E' := E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)), is strongly connected and player \<alpha> wins all cycles in (U,E').
    We will work with several variations of this definition. *)
section \<open>Tangle Definitions\<close>

(** We will need a definition for a tangle tied to a specific player for future proofs.
    We start by working from this definition; we will tie it to the general definition as given by
    Van Dijk later *)
subsection \<open>Tangles for a specific player\<close>
context player_paritygame
begin
  (** As defined by Van Dijk, a tangle's subgraph E' is equal to E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)) *)
  definition player_tangle_subgraph :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v dgraph" where
    "player_tangle_subgraph U \<sigma> = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V\<^sub>\<beta>) \<times> U)"

  (** Van Dijk's definition of a tangle's subgraph E' is the same as the induced subgraph of
      the tangle strategy over its domain, restricted to U.
      This equality makes it easier to use tangle definitions with lemmas for general parity games. *)
  lemma player_tangle_subgraph_is_restricted_ind_subgraph:
    assumes "U \<subseteq> V"
    assumes "dom \<sigma> = U \<inter> V\<^sub>\<alpha>"
    assumes "ran \<sigma> \<subseteq> U"
    shows "player_tangle_subgraph U \<sigma> = induced_subgraph (dom \<sigma>) \<sigma> \<inter> (U\<times>U)"
    unfolding player_tangle_subgraph_def induced_subgraph_def E_of_strat_def
    using assms by (auto simp: ranI)

  (** We say that a strategy is a tangle strategy if it belongs to the player, is of the form
      \<sigma>: U\<^sub>\<alpha> \<longrightarrow> U, and the graph (U,E'), with E' := E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)), is strongly connected and
      the player wins all cycles in (U,E'). *)
  definition is_player_tangle_strat :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
    "is_player_tangle_strat U \<sigma> \<equiv> strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V\<^sub>\<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
     (let E' = player_tangle_subgraph U \<sigma> in (
        strongly_connected E' \<and>
        (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> winning_player xs)
     ))"

  (** We can then say that a tangle for a player is a nonempty set of vertices U in V, where
      the player wins pr(U), and there exists a strategy \<sigma> that is a tangle strategy for the player. *)
  definition player_tangle :: "'v set \<Rightarrow> bool" where
    "player_tangle U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> winningP (pr_set U) \<and> (\<exists>\<sigma>. is_player_tangle_strat U \<sigma>)"

  lemma player_tangle_notempty[simp]: "\<not>player_tangle {}"
    unfolding player_tangle_def by simp

  lemma player_tangle_in_V: "player_tangle U \<Longrightarrow> U \<subseteq> V"
    unfolding player_tangle_def by simp

  (** Van Dijk observes that a tangle from which the opponent cannot escape is a dominion (which we
      call a winning region). Proving this shows that our definition matches his, and this property
      may be useful in future proofs. *)
  lemma closed_player_tangle_is_winning_region:
    assumes player_tangle: "player_tangle U"
    assumes U_closed_opp: "E `` (U \<inter> V\<^sub>\<beta>) \<subseteq> U"
    shows "player_winning_region U"
  proof -
    from player_tangle_in_V[OF player_tangle]
    have U_in_V: "U \<subseteq> V" .

    from player_tangle obtain \<sigma> where
        \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>"
    and \<sigma>_dom: "dom \<sigma> = U \<inter> V\<^sub>\<alpha>"
    and \<sigma>_ran: "ran \<sigma> \<subseteq> U"
    and \<sigma>_winning: "\<forall>v\<in>U. \<forall>xs. cycle_node (player_tangle_subgraph U \<sigma>) v xs \<longrightarrow> winning_player xs"
      unfolding player_tangle_def is_player_tangle_strat_def Let_def by auto

    have \<sigma>_winning_subgraph: "\<forall>u\<in>U. \<forall>ys. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) u ys
        \<longrightarrow> winning_player ys"
    proof (rule ballI; rule allI; rule impI)
      fix u ys
      assume u_in_U: "u \<in> U" and cycle_u_ys: "cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) u ys"

      from \<sigma>_dom U_closed_opp have "induced_subgraph (dom \<sigma>) \<sigma> `` U \<subseteq> U"
        using ind_subgraph_closed_region[OF U_in_V _ \<sigma>_ran, of "dom \<sigma>"] by blast
      from cycle_from_node_closed_set[OF u_in_U this cycle_u_ys]
      have ys_in_U: "set ys \<subseteq> U" .

      from cycle_u_ys ys_in_U obtain y where
          cycle_y_ys: "cycle_node (induced_subgraph (dom \<sigma>) \<sigma>) y ys"
      and y_in_U: "y \<in> U"
        unfolding cycle_from_node_def
        using origin_in_cycle_node by fastforce

      have "induced_subgraph (dom \<sigma>) \<sigma> \<inter> (U\<times>U) \<subseteq> player_tangle_subgraph U \<sigma>"
        using player_tangle_subgraph_is_restricted_ind_subgraph[OF U_in_V \<sigma>_dom \<sigma>_ran] by simp
        from \<sigma>_winning y_in_U subgraph_cycle[OF this cycle_restr_V[OF cycle_y_ys ys_in_U]]
        show "winning_player ys" by simp
    qed

    show ?thesis
      unfolding player_winning_region_def
      apply (simp add: U_in_V)
      apply (rule exI[where x="\<sigma>"]; intro conjI)
        subgoal using \<sigma>_strat .
        subgoal using \<sigma>_dom Int_commute ..
        subgoal using \<sigma>_ran .
        subgoal using \<sigma>_winning_subgraph .
        subgoal using U_closed_opp by fast
      done
  qed
end

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

  definition tangle :: "'v set \<Rightarrow> bool" where
    "tangle U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and>
    (let \<alpha> = player_wins_pr (pr_set U) in (
      \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
      (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
        strongly_connected E' \<and>
        (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
    ))))"

  lemma tangle_iff_p_tangle: "tangle U \<longleftrightarrow> p_tangle (pr_set U) U"
    unfolding tangle_def p_tangle_def pr_set_def Let_def by auto

  lemma tangle_notempty[simp]: "\<not>tangle {}"
    unfolding tangle_def by simp

  lemma tangle_in_V: "tangle U \<Longrightarrow> U \<subseteq> V"
    unfolding tangle_def by simp

  fun tangle_player :: "player \<Rightarrow> 'v set \<Rightarrow> bool" where
    "tangle_player EVEN = P0.player_tangle"
  | "tangle_player ODD = P1.player_tangle"

  lemma closed_tangle_player_is_winning_region:
    assumes tangle_player_U: "tangle_player \<alpha> U"
    assumes U_closed_opp: "E `` (U \<inter> V_opponent \<alpha>) \<subseteq> U"
    shows "winning_region \<alpha> U"
    using assms P0.closed_player_tangle_is_winning_region P1.closed_player_tangle_is_winning_region
    by (cases \<alpha>; simp add: V\<^sub>1_def V_diff_diff_V\<^sub>0)

  lemma tangle_player_iff_tangle: "tangle_player \<alpha> U \<longleftrightarrow> (\<alpha> = player_wins_pr (pr_set U) \<and> tangle U)"
    using P0.is_player_tangle_strat_def P1.is_player_tangle_strat_def
    using P0.player_tangle_def P1.player_tangle_def
    using P0.player_tangle_subgraph_def P1.player_tangle_subgraph_def
    unfolding tangle_def Let_def strategy_of_player_def player_wins_pr_def
    by (cases \<alpha>; simp add: V\<^sub>1_def V_diff_diff_V\<^sub>0)

  lemma closed_tangle_is_winning_region:
    assumes tangle_U: "tangle U"
    assumes U_closed_opp: "E `` (U \<inter> V_opponent (player_wins_pr(pr_set U))) \<subseteq> U"
    shows "winning_region (player_wins_pr (pr_set U)) U"
    using assms tangle_player_iff_tangle closed_tangle_player_is_winning_region by simp

  definition tangle_strat :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "tangle_strat U \<sigma> \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and>
   (let \<alpha> = player_wins_pr (pr_set U) in (
      strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
        (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
          strongly_connected E' \<and>
          (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
   ))))"

  lemma tangle_iff_tangle_strat:"tangle U \<longleftrightarrow> (\<exists>\<sigma>. tangle_strat U \<sigma>)"
    unfolding tangle_def tangle_strat_def Let_def
    by auto

  lemma tangle_strat_notempty[simp]: "\<not>tangle_strat {} \<sigma>"
    unfolding tangle_strat_def by simp

  lemma tangle_strat_in_V: "tangle_strat U \<sigma> \<Longrightarrow> U \<subseteq> V"
    unfolding tangle_strat_def by simp

  lemma closed_tangle_strat_is_winning_region:
    assumes tangle: "tangle_strat U \<sigma>"
    assumes closed_opp: "\<forall>u \<in> U. u \<in> V_opponent (player_wins_pr(pr_set U)) \<longrightarrow> E `` {u} \<subseteq> U"
    shows "winning_region (player_wins_pr (pr_set U)) U"
    using assms tangle_iff_tangle_strat closed_tangle_is_winning_region by blast
end

context player_paritygame
begin

  definition opponent_escapes :: "'v set \<Rightarrow> 'v set" where
    "opponent_escapes t \<equiv> {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V\<^sub>\<beta> \<and> v \<in> V - t}"

  lemma opponent_escapes_in_V: "opponent_escapes t \<subseteq> V"
    unfolding opponent_escapes_def by auto

  lemma fin_opponent_escapes: "finite (opponent_escapes t)"
    using finite_subset[OF opponent_escapes_in_V fin_V] .

  lemma player_tangle_escapes: "player_tangle U
    \<Longrightarrow> (\<forall>v\<in>U \<inter> V\<^sub>\<beta>. \<forall>w. (v,w) \<in> E \<longrightarrow> w \<in> U \<or> w \<in> opponent_escapes U)"
    unfolding opponent_escapes_def
    using E_in_V by auto

  lemma map_asym_add_tangle_strats:
    assumes t1_in_V: "t1 \<subseteq> V"
    assumes t1_no_escapes_t2: "\<forall>v \<in> opponent_escapes t1. v \<notin> t2"
    assumes \<sigma>_dom: "dom \<sigma> = t1 \<inter> V\<^sub>\<alpha>"
    assumes \<sigma>_ran: "ran \<sigma> \<subseteq> t1"
    assumes \<sigma>_winning_t1: "\<forall>v\<in>t1. \<forall>xs. cycle_node (player_tangle_subgraph t1 \<sigma>) v xs \<longrightarrow> winning_player xs"
    assumes t2_in_V: "t2 \<subseteq> V"
    assumes \<sigma>'_dom: "dom \<sigma>' = t2 \<inter> V\<^sub>\<alpha>"
    assumes \<sigma>'_ran: "ran \<sigma>' \<subseteq> t2"
    assumes \<sigma>'_winning_t2: "\<forall>v\<in>t2. \<forall>xs. cycle_node (player_tangle_subgraph t2 \<sigma>') v xs \<longrightarrow> winning_player xs"
    shows "\<forall>v\<in>t1\<union>t2. \<forall>xs. cycle_node (player_tangle_subgraph (t1\<union>t2) (\<sigma>' ++ \<sigma>)) v xs \<longrightarrow> winning_player xs"
  proof (rule ballI; rule allI; rule impI)
    fix v xs
    assume v_in_union: "v\<in>t1\<union>t2"
       and cycle_v_xs: "cycle_node  (player_tangle_subgraph (t1\<union>t2) (\<sigma>' ++ \<sigma>)) v xs"

    let ?E' = "player_tangle_subgraph (t1\<union>t2) (\<sigma>' ++ \<sigma>)"

    from \<sigma>_dom \<sigma>'_dom have comb_dom: "dom (\<sigma>' ++ \<sigma>) = (t1\<union>t2) \<inter> V\<^sub>\<alpha>" by force

    from \<sigma>_ran \<sigma>'_ran have comb_ran: "ran (\<sigma>' ++ \<sigma>) \<subseteq> t1\<union>t2"
      unfolding ran_def using ranI by fast

    have E'_closed_t1: "?E' `` t1 \<subseteq> t1"
    proof (rule subsetI)
      fix y
      assume y_succ_t1: "y \<in> ?E' `` t1"
      then obtain x where x_in_t1: "x \<in> t1" and edge_in_E': "(x,y)\<in>?E'" by blast

      from x_in_t1 t1_in_V consider (x_player) "x \<in> t1 \<inter> V\<^sub>\<alpha>" | (x_opponent) "x \<in> t1 \<inter> V\<^sub>\<beta>" by fast
      then show "y \<in> t1" proof cases
        case x_player
        with comb_dom edge_in_E' \<sigma>_dom have "\<sigma> x = Some y"
          unfolding player_tangle_subgraph_def E_of_strat_def by blast
        with \<sigma>_ran show ?thesis
          using ranI[of \<sigma>] by blast
      next
        case x_opponent
        with t1_no_escapes_t2 t2_in_V edge_in_E' comb_dom show ?thesis
          unfolding opponent_escapes_def player_tangle_subgraph_def E_of_strat_def by auto
      qed
    qed

    have E'_partially_closed_t2: "?E' `` t2 \<subseteq> t1\<union>t2"
    proof (rule subsetI)
      fix y
      assume y_succ_t2: "y \<in> ?E' `` t2"
      then obtain x where x_in_t2: "x\<in>t2" and edge_in_E': "(x,y)\<in>?E'" by blast

      from x_in_t2 t2_in_V consider (x_player) "x \<in> t2 \<inter> V\<^sub>\<alpha>" | (x_opponent) "x \<in> t2 \<inter> V\<^sub>\<beta>" by fast
      then show "y \<in> t1\<union>t2" proof cases
        case x_player
        with edge_in_E' comb_dom have "(\<sigma>' ++ \<sigma>) x = Some y"
          unfolding player_tangle_subgraph_def E_of_strat_def by fast
        with comb_ran show ?thesis
          using ranI[of "\<sigma>' ++ \<sigma>" x y] by fast
      next
        case x_opponent
        with t2_in_V edge_in_E' comb_dom show ?thesis
          unfolding player_tangle_subgraph_def E_of_strat_def by auto
      qed
    qed

    have E'_closed_union: "?E' `` (t1\<union>t2) \<subseteq> t1\<union>t2"
      using E'_closed_t1 E'_partially_closed_t2 by blast

    from cycle_node_closed_set[OF v_in_union E'_closed_union cycle_v_xs]
    have xs_in_union: "set xs \<subseteq> t1 \<union> t2" .

    consider (v_in_t1) "v\<in>t1" | (v_notin_t1) "v\<notin>t1" by blast
    thus "winning_player xs" proof cases
      case v_in_t1
      from cycle_node_closed_set[OF v_in_t1 E'_closed_t1 cycle_v_xs]
      have xs_in_t1: "set xs \<subseteq> t1" .

      from t1_in_V \<sigma>_dom have "(?E' \<inter> t1\<times>t1) \<subseteq> player_tangle_subgraph t1 \<sigma>"
        unfolding player_tangle_subgraph_def E_of_strat_def by auto
      from subgraph_cycle[OF this cycle_restr_V[OF cycle_v_xs xs_in_t1]]
      have "cycle_node (player_tangle_subgraph t1 \<sigma>) v xs" .

      with \<sigma>_winning_t1 v_in_t1 show ?thesis by blast

    next
      case v_notin_t1
      with v_in_union have v_in_t2: "v\<in>t2" by fast
      with v_notin_t1 have v_in_t2_min_t1: "v \<in> t2-t1" by fast

      consider (t1_notin_xs) "set xs \<inter> t1 = {}" | (t1_in_xs) "set xs \<inter> t1 \<noteq> {}" by fast
      thus ?thesis proof cases
        case t1_notin_xs
        with xs_in_union have xs_in_t2_min_t1: "set xs \<subseteq> t2-t1" by blast

        from t2_in_V \<sigma>_dom \<sigma>'_dom have "(?E' \<inter> (t2-t1)\<times>(t2-t1)) \<subseteq> player_tangle_subgraph t2 \<sigma>'"
          unfolding player_tangle_subgraph_def E_of_strat_def by auto
        from subgraph_cycle[OF this cycle_restr_V[OF cycle_v_xs xs_in_t2_min_t1]]
        have "cycle_node (player_tangle_subgraph t2 \<sigma>') v xs" .

        with v_in_t2_min_t1 \<sigma>'_winning_t2 show ?thesis by fast

      next
        case t1_in_xs
        then obtain w xs' where
          w_in_xs: "w \<in> set xs" and w_in_t1: "w \<in> t1" and
          xs'_xs_sets_eq: "set xs' = set xs" and cycle_w_xs': "cycle_node ?E' w xs'"
          using cycle_node_intermadiate_node[OF cycle_v_xs] by blast

        from xs'_xs_sets_eq cycle_node_closed_set[OF w_in_t1 E'_closed_t1 cycle_w_xs']
        have xs_in_t1: "set xs \<subseteq> t1" by fast
        from cycle_v_xs have v_in_xs: "v \<in> set xs" using origin_in_cycle_node by fast

        from xs_in_t1 v_in_xs have v_in_t1: "v \<in> t1" by blast
        with v_notin_t1 show ?thesis by fast
      qed
    qed
  qed

  definition asym_combine :: "('v set \<times> 'v strat) list \<Rightarrow> 'v strat" where
    "asym_combine xs \<equiv> foldr (\<lambda>x y. snd x ++ y) xs Map.empty"

  lemma foldr_asym_add_dom: "dom (foldr (\<lambda>x y. snd x ++ y) xs \<sigma>) = dom \<sigma> \<union> \<Union>(dom ` snd ` set xs)"
    by (induction xs arbitrary: \<sigma>) auto

  lemma asym_combine_dom: "dom (asym_combine xs) = \<Union>(dom ` snd ` set xs)"
    unfolding asym_combine_def using foldr_asym_add_dom[of xs Map.empty] by simp

  lemma foldr_asym_add_ran: "ran (foldr (\<lambda>x y. snd x ++ y) xs \<sigma>) \<subseteq> ran \<sigma> \<union> \<Union>(ran ` snd ` set xs)"
    apply (induction xs arbitrary: \<sigma>; simp)
    unfolding ran_def using ranI by auto

  lemma asym_combine_ran: "ran (asym_combine xs) \<subseteq> \<Union>(ran ` snd ` set xs)"
    unfolding asym_combine_def using foldr_asym_add_ran[of xs Map.empty] by simp

  lemma foldr_asym_add_strategy_of:  "\<lbrakk>\<forall>\<sigma>\<in>snd`set xs. strategy_of V\<^sub>\<alpha> \<sigma>; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk>
    \<Longrightarrow> strategy_of V\<^sub>\<alpha> (foldr (\<lambda>x y. snd x ++ y) xs \<sigma>)"
    by (induction xs arbitrary: \<sigma>) auto

  lemma asym_combine_strategy_of:
    "\<forall>\<sigma>\<in>snd`set xs. strategy_of V\<^sub>\<alpha> \<sigma> \<Longrightarrow> strategy_of V\<^sub>\<alpha> (asym_combine xs)"
    unfolding asym_combine_def using foldr_asym_add_strategy_of[of xs Map.empty] by simp

  lemma asym_combine_prepend: "asym_combine (x#xs) = snd x ++ asym_combine xs"
    unfolding asym_combine_def by simp

  lemma set_list_union: "\<Union>(fst ` set xs) \<union> fst x = \<Union>(fst ` set (x#xs))" by auto

  lemma asym_combine_tangle_strats:
    fixes xs :: "('v set \<times> 'v strat) list"
    assumes "\<forall>s\<in>fst ` set xs. s \<subseteq> V"
    assumes "\<forall>s1\<in>fst ` set xs. \<forall>s2\<in>fst ` set xs. \<forall>v \<in> opponent_escapes s1. v \<notin> s2"
    assumes "\<forall>(s,\<sigma>)\<in>set xs. is_player_tangle_strat s \<sigma>"
    shows "\<forall>v\<in>\<Union>(fst ` set xs). \<forall>vs. cycle_node (player_tangle_subgraph (\<Union>(fst ` set xs)) (asym_combine xs)) v vs \<longrightarrow> winning_player vs"
    using assms
  proof (induction xs)
    case Nil thus ?case by simp
  next
    case (Cons a xs)

    let ?S = "fst ` set xs"
    let ?a = "fst a"
    let ?\<sigma> = "snd a"

    from Cons.prems(1) have in_S_in_V: "\<forall>s\<in>?S. s \<subseteq> V" by simp
    from Cons.prems(2) have no_escapes_S: "\<forall>s1\<in>?S. \<forall>s2\<in>?S. \<forall>v\<in>opponent_escapes s1. v\<notin>s2" by auto
    from Cons.prems(3) have tangles_xs: "\<forall>(s,\<sigma>)\<in>set xs. is_player_tangle_strat s \<sigma>" by auto
    note IH = Cons.IH[OF in_S_in_V no_escapes_S tangles_xs]

    from in_S_in_V have S_in_V: "\<Union>?S \<subseteq> V" by blast

    have no_escapes_to_a: "\<forall>v \<in> opponent_escapes (\<Union>?S). v \<notin> ?a"
    proof (rule ballI)
      fix v
      assume v_escape: "v \<in> opponent_escapes (\<Union>?S)"
      then obtain s1 where s1_in_xs: "s1 \<in> ?S" and v_escapes_s1: "v \<in> opponent_escapes s1"
        unfolding opponent_escapes_def by blast
      from Cons.prems(2) s1_in_xs v_escapes_s1
      show "v \<notin> ?a" by force
    qed

    have dom_combine_xs: "dom (asym_combine xs) = \<Union>?S \<inter> V\<^sub>\<alpha>"
    proof -
      from tangles_xs have "\<forall>(s',\<sigma>')\<in>set xs. dom \<sigma>' = s' \<inter> V\<^sub>\<alpha>"
        unfolding is_player_tangle_strat_def by fast
      hence "\<Union>(dom ` (snd ` set xs)) = \<Union>?S \<inter> V\<^sub>\<alpha>"
        by (simp add: case_prod_beta)
      thus ?thesis
        using asym_combine_dom by auto
    qed

    have ran_combine_xs: "ran (asym_combine xs) \<subseteq> \<Union>?S"
    proof -
      from tangles_xs have "\<forall>(s',\<sigma>')\<in>set xs. ran \<sigma>' \<subseteq> s'"
        unfolding is_player_tangle_strat_def by fast
      hence "\<Union>(ran ` (snd ` set xs)) \<subseteq> \<Union>(fst ` set xs)"
        by simp force
      thus ?thesis
        using asym_combine_ran by fast
    qed

    from Cons.prems(1) have a_in_V: "?a \<subseteq> V" by simp
    from Cons.prems(3) have \<sigma>_dom: "dom ?\<sigma> = ?a \<inter> V\<^sub>\<alpha>"
      unfolding is_player_tangle_strat_def by simp force
    from Cons.prems(3) have \<sigma>_ran: "ran ?\<sigma> \<subseteq> ?a"
      unfolding is_player_tangle_strat_def by force
    from Cons.prems(3) have \<sigma>_winning_a:
      "\<forall>v\<in>?a. \<forall>xs. cycle_node (player_tangle_subgraph ?a ?\<sigma>) v xs \<longrightarrow> winning_player xs"
      unfolding is_player_tangle_strat_def Let_def by force

    from map_asym_add_tangle_strats
      [OF S_in_V no_escapes_to_a dom_combine_xs ran_combine_xs IH a_in_V \<sigma>_dom \<sigma>_ran \<sigma>_winning_a]
    show ?case by (simp add: set_list_union asym_combine_prepend)
  qed

  lemma tangle_strats_list:
    assumes fin_S: "finite S"
    assumes tangles_S: "\<forall>t\<in>S. player_tangle t"
    shows "\<exists>xs :: ('v set\<times>'v strat) list. length xs = card S \<and>
                                          \<Union>(fst`set xs) = \<Union>S \<and>
                                          (\<forall>s\<in>fst`set xs. s\<in>S) \<and>
                                          (\<forall>(t,\<sigma>)\<in>set xs. is_player_tangle_strat t \<sigma>)"
  proof -
    define t_strat where "t_strat = (\<lambda>t. SOME \<sigma>. is_player_tangle_strat t \<sigma>)"

    {
      fix t
      assume "t\<in>S"
      with tangles_S have \<sigma>_exI: "\<exists>\<sigma>. is_player_tangle_strat t \<sigma>"
        unfolding player_tangle_def Let_def by fast
      have "is_player_tangle_strat t (t_strat t)"
        using someI_ex[OF \<sigma>_exI]
        unfolding t_strat_def .
    } note S_strat=this

    obtain S_list where S_list_set: "set S_list = S" and S_list_len: "length S_list = card S"
      using finite_distinct_list[OF fin_S] distinct_card by fastforce

    define xs :: "('v set \<times> 'v strat) list" where
      "xs = map (\<lambda>t. Pair t (t_strat t)) S_list"

    show ?thesis proof (rule exI[where x="xs"]; intro conjI)
      from S_list_len show "length xs = card S"
        unfolding xs_def by simp
    next
      from S_list_set show "\<Union>(fst`set xs) = \<Union>S"
        unfolding xs_def by auto
    next
      from S_list_set show "\<forall>s\<in>fst ` set xs. s \<in> S"
        unfolding xs_def by simp
    next
      from S_list_set show "\<forall>(x,y)\<in>set xs. is_player_tangle_strat x y"
        unfolding xs_def by (simp add: S_strat)
    qed
  qed

  lemma combined_tangle_strat:
    assumes fin_S: "finite S"
    assumes tangles_S: "\<forall>t\<in>S. player_tangle t"
    assumes no_escapes_S: "\<forall>t1\<in>S. \<forall>t2\<in>S. \<forall>v\<in>opponent_escapes t1. v\<notin>t2"
    shows "\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
               dom \<sigma> = \<Union>S \<inter> V\<^sub>\<alpha> \<and>
               ran \<sigma> \<subseteq> \<Union>S \<and>
               (\<forall>v\<in>\<Union>S. \<forall>xs. cycle_node (player_tangle_subgraph (\<Union>S) \<sigma>) v xs \<longrightarrow> winning_player xs)"
  proof -
    from tangle_strats_list[OF fin_S tangles_S] obtain xs where
      xs_len: "length xs = card S" and
      xs_set: "\<Union>(fst`set xs) = \<Union>S" and
      xs_in_S: "\<forall>s\<in>fst ` set xs. s \<in> S" and
      xs_tangle_strats: "\<forall>(x, y)\<in>set xs. is_player_tangle_strat x y"
      by auto

    from tangles_S xs_set have xs_in_V: "\<forall>s\<in>fst`set xs. s\<subseteq>V"
      unfolding player_tangle_def by blast

    from no_escapes_S xs_in_S
    have no_escapes_xs: "\<forall>t1\<in>fst`set xs. \<forall>t2\<in>fst`set xs. \<forall>v\<in>opponent_escapes t1. v\<notin>t2"
      by blast

    define \<sigma> where "\<sigma> = asym_combine xs"

    show ?thesis proof (rule exI[where x="\<sigma>"]; intro conjI ballI allI impI)
      from xs_tangle_strats have "\<forall>\<sigma>\<in>snd`set xs. strategy_of V\<^sub>\<alpha> \<sigma>"
        unfolding is_player_tangle_strat_def by auto
      from asym_combine_strategy_of[OF this] show "strategy_of V\<^sub>\<alpha> \<sigma>"
        unfolding \<sigma>_def .

    next
      from xs_tangle_strats have "\<forall>x\<in>set xs. dom (snd x) = (fst x) \<inter> V\<^sub>\<alpha>"
        unfolding is_player_tangle_strat_def by fastforce
      with xs_set show "dom \<sigma> = \<Union>S \<inter> V\<^sub>\<alpha>"
        unfolding \<sigma>_def using asym_combine_dom[of xs] by simp

    next
      from xs_tangle_strats have "\<forall>x\<in>set xs. ran (snd x) \<subseteq> \<Union>(fst`set xs)"
        unfolding is_player_tangle_strat_def by force
      with xs_set show "ran \<sigma> \<subseteq> \<Union>S"
        unfolding \<sigma>_def using asym_combine_ran[of xs] by fastforce

    next
      fix v vs
      assume v_in_S: "v\<in>\<Union>S" and
             cycle_v_xs: "cycle_node (player_tangle_subgraph (\<Union>S) \<sigma>) v vs"
      with xs_set show "winning_player vs"
        unfolding \<sigma>_def
        using asym_combine_tangle_strats[OF xs_in_V no_escapes_xs xs_tangle_strats] by force
    qed
  qed

  context
    fixes T :: "'v set set"
    assumes tangles_T : "\<forall>t\<in>T. player_tangle t"
    assumes finite_T: "finite T"
  begin

    inductive_set player_tangle_attractor :: "'v set \<Rightarrow> 'v set" for A where
      base: "x \<in> A \<Longrightarrow> x \<in> player_tangle_attractor A"
    | own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-A; (x,y) \<in> E; y \<in> player_tangle_attractor A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor A"
    | opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-A; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> player_tangle_attractor A\<rbrakk>
                  \<Longrightarrow> x \<in> player_tangle_attractor A"
    | escape: "\<lbrakk>x \<in> t; t \<in> T; t \<inter> A = {}; opponent_escapes t \<noteq> {};
                \<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> player_tangle_attractor A\<rbrakk>
                \<Longrightarrow> x \<in> player_tangle_attractor A"

    lemma player_tangle_attractor_subset[simp]: "A \<subseteq> player_tangle_attractor A"
      by (auto intro: player_tangle_attractor.base)

    definition \<alpha>_maximal :: "'v set \<Rightarrow> bool" where
      "\<alpha>_maximal A \<equiv> A = player_tangle_attractor A"

    context
      fixes A :: "'v set"
    begin
      abbreviation player_target_nodes where
        "player_target_nodes S \<equiv> { x | x y :: 'v. x\<in>V\<^sub>\<alpha> - A \<and> (x,y)\<in>E \<and> y\<in>S }"

      abbreviation opponent_forced_nodes where
      "opponent_forced_nodes S \<equiv> { x. x\<in>V\<^sub>\<beta> - A \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>S) }"

      abbreviation tangle_escape_nodes where
        "tangle_escape_nodes S \<equiv> { x | x t. x\<in>t - A  \<and> t\<in>T \<and> opponent_escapes t \<noteq> {} \<and>
            (\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v\<in>S)} - player_target_nodes S - opponent_forced_nodes S"

      (*fun tangle_nodes_in_rank :: "nat \<Rightarrow> 'v set" where
        "tangle_nodes_in_rank 0 = A"
      | "tangle_nodes_in_rank (Suc n) =
         tangle_nodes_in_rank n
         \<union> player_target_nodes (tangle_nodes_in_rank n)
         \<union> opponent_forced_nodes (tangle_nodes_in_rank n)
         \<union> tangle_escape_nodes (tangle_nodes_in_rank n)"*)

      fun tangle_nodes_in_rank :: "nat \<Rightarrow> 'v set" where
        "tangle_nodes_in_rank 0 = A"
      | "tangle_nodes_in_rank (Suc n) =
         tangle_nodes_in_rank n
         \<union> { x | x y :: 'v. x\<in>V\<^sub>\<alpha> - A \<and> (x,y)\<in>E \<and> y\<in>tangle_nodes_in_rank n }
         \<union> { x. x\<in>V\<^sub>\<beta> - A \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>tangle_nodes_in_rank n) }
         \<union> { x | x t. x\<in>t \<and> t \<inter> A = {} \<and> t\<in>T \<and> opponent_escapes t \<noteq> {} \<and>
            (\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v\<in>tangle_nodes_in_rank n) }"

      lemma tangle_nodes_in_rank_Suc_cases:
        assumes "x \<in> tangle_nodes_in_rank (Suc n)"
        obtains (base) "x \<in> tangle_nodes_in_rank n"
        | (own) "x \<in> V\<^sub>\<alpha> - A \<and> (\<exists>y. (x,y)\<in>E \<and> y \<in> tangle_nodes_in_rank n)"
        | (opponent) "x \<in> V\<^sub>\<beta> - A \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>tangle_nodes_in_rank n)"
        | (escape) "\<exists>t. x \<in> t \<and> t \<inter> A = {} \<and> t \<in> T \<and> opponent_escapes t \<noteq> {} \<and>
                    (\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> tangle_nodes_in_rank n)"
        using assms by auto

      lemma all_escape_tangles_in_same_rank:
        assumes "t \<inter> A = {} \<and>  t\<in>T \<and> opponent_escapes t \<noteq> {} \<and>
          (\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> tangle_nodes_in_rank n)"
        shows "\<forall>x\<in>t. x\<in>tangle_nodes_in_rank (Suc n)"
        using assms by auto

      lemma A_notin_tangle_nodes_in_rank_Suc_nodes:
        "(tangle_nodes_in_rank (Suc n) - tangle_nodes_in_rank n) \<inter> A = {}"
        by force

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
            subgoal using player_tangle_attractor.escape subset_iff[of _ "player_tangle_attractor A"] by force
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
              x_in_t: "x \<in> t"
          and t_notin_A: "t \<inter> A = {}"
          and t_in_T: "t \<in> T"
          and t_has_escapes: "opponent_escapes t \<noteq> {}"
          and escapes_in_n: "\<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> tangle_nodes_in_rank n"
            by blast

          from t_in_T have t_tangle: "player_tangle t" using tangles_T by fast

          from Suc.prems(3,4) have "x \<in> V\<^sub>\<beta>" using E_in_V by blast
          with x_in_t have x_in_V\<^sub>\<beta>_U_t: "x \<in> V\<^sub>\<beta> \<inter> t" by blast
          with t_tangle Suc.prems(3) have "y \<in> t \<or> y \<in> opponent_escapes t"
            using player_tangle_escapes by blast

          with t_notin_A t_in_T t_has_escapes escapes_in_n show ?thesis
            using tangle_nodes_in_rank_subset by clarsimp blast
        qed
      qed

      (** There are two possibilities with tangle attractors: either they force a play to A,
          or the player wins the play because it stays in a tangle for that player.
          TODO: path starts in n
            - if the path stays in n, the player has won
            - if the path leaves n, then eventually it reaches A. *)
      lemma tangle_nodes_in_rank_forces_A_or_wins: "\<exists>\<sigma>.
        strategy_of V\<^sub>\<alpha> \<sigma>
        \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (tangle_nodes_in_rank n - A) \<and> ran \<sigma> \<subseteq> tangle_nodes_in_rank n
        \<and> (\<forall>m. \<forall>x \<in> tangle_nodes_in_rank m - A. (\<forall>y \<in> (induced_subgraph V\<^sub>\<alpha> \<sigma>) `` {x}. y \<in> tangle_nodes_in_rank m))
        \<and> (\<forall>x \<in> tangle_nodes_in_rank n. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
              \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"
      proof (induction n)
        case 0 thus ?case
          apply (rule exI[where x="Map.empty"])
          apply (intro conjI; simp)
            subgoal using tangle_nodes_in_rank_edges_same by blast
            subgoal using origin_in_lasso by fast
          done
      next
        case (Suc n)
        from Suc.IH obtain \<sigma> where
            \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>"
        and \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (tangle_nodes_in_rank n - A)"
        and \<sigma>_ran: "ran \<sigma> \<subseteq> tangle_nodes_in_rank n"
        and \<sigma>_closed_rank: "\<forall>m. \<forall>x\<in>tangle_nodes_in_rank m - A. \<forall>y\<in>induced_subgraph V\<^sub>\<alpha> \<sigma> `` {x}. y \<in> tangle_nodes_in_rank m"
        and \<sigma>_forces_A_or_wins: "\<forall>x \<in> tangle_nodes_in_rank n. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
              \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys)"
          by auto

        let ?new_nodes = "(tangle_nodes_in_rank (Suc n) - tangle_nodes_in_rank n)"
        have new_nodes_in_V: "?new_nodes \<subseteq> V"
          using tangles_T V\<^sub>\<alpha>_subset unfolding player_tangle_def by auto
        from finite_subset[OF this fin_V] have fin_new_nodes: "finite ?new_nodes" .
        have new_nodes_no_A: "?new_nodes \<inter> A = {}"
          using A_notin_tangle_nodes_in_rank_Suc_nodes by blast

        define new_player_nodes where
          "new_player_nodes = {x | x y. x\<in>?new_nodes \<inter> V\<^sub>\<alpha> \<and> (x,y)\<in>E \<and> y\<in>tangle_nodes_in_rank n}"

        define new_opponent_nodes where
          "new_opponent_nodes = {x. x\<in>?new_nodes \<inter> V\<^sub>\<beta> \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>tangle_nodes_in_rank n)}"

        define new_escape_nodes where
          "new_escape_nodes = {x | x t. x\<in>?new_nodes \<and> x\<in>t \<and> t \<inter> A = {} \<and> t\<in>T \<and>
            opponent_escapes t \<noteq> {} \<and> (\<forall>v. v\<in>opponent_escapes t \<longrightarrow> v\<in>tangle_nodes_in_rank n)}"

        define new_escape_tangles where
          "new_escape_tangles = {t. t \<inter> A = {} \<and> t\<in>T \<and>
           opponent_escapes t \<noteq> {} \<and> (\<forall>v. v\<in>opponent_escapes t \<longrightarrow> v\<in>tangle_nodes_in_rank n)}"

        have "new_escape_nodes \<subseteq> \<Union>new_escape_tangles"
          unfolding new_escape_nodes_def new_escape_tangles_def by blast

        have "new_escape_nodes = \<Union>new_escape_tangles \<longleftrightarrow>
          \<Union>new_escape_tangles \<inter> tangle_nodes_in_rank n = {}"
          unfolding new_escape_nodes_def new_escape_tangles_def
          apply (rule iffI; simp) by blast+

        have "\<forall>t1\<in>new_escape_tangles. \<forall>t2\<in>new_escape_tangles. \<forall>v\<in>opponent_escapes t1. v \<notin> t2"
          unfolding new_escape_tangles_def opponent_escapes_def
          apply (intro ballI; clarsimp)
          subgoal for t1 t2 v u x x' y y' sorry

        have new_nodes_comp: "?new_nodes = new_player_nodes \<union> new_opponent_nodes \<union> new_escape_nodes"
          unfolding new_player_nodes_def new_opponent_nodes_def new_escape_nodes_def by simp blast

        hence "?new_nodes - new_escape_nodes \<subseteq> new_player_nodes \<union> new_opponent_nodes"
          by blast

        (** These obviously do not overlap *)
        have "new_player_nodes \<inter> new_opponent_nodes = {}"
          unfolding new_player_nodes_def new_opponent_nodes_def by blast

        (** But these might, though they do not have to, so I can't prove either direction.*)
(**
        have "new_player_nodes \<inter> new_escape_nodes = {}"
          unfolding new_player_nodes_def new_escape_nodes_def
          sorry
        have "new_player_nodes \<inter> new_escape_nodes \<noteq> {}"
          unfolding new_player_nodes_def new_escape_nodes_def
          sorry

        have "new_opponent_nodes \<inter> new_escape_nodes = {}"
          unfolding new_opponent_nodes_def new_escape_nodes_def
          sorry
        have "new_opponent_nodes \<inter> new_escape_nodes \<noteq> {}"
          unfolding new_opponent_nodes_def new_escape_nodes_def
          sorry
*)
        define new_tangles where "new_tangles = {t. t \<subseteq> ?new_nodes \<and> t \<inter> A = {} \<and> t\<in>T \<and>
            opponent_escapes t \<noteq> {} \<and> (\<forall>v. v\<in>opponent_escapes t \<longrightarrow> v\<in>tangle_nodes_in_rank n)}"

        have new_tangles_in_new_escape_nodes: "\<Union>new_tangles \<subseteq> new_escape_nodes"
          unfolding new_tangles_def new_escape_nodes_def by blast

        define target where "target = (\<lambda>x. SOME y. y\<in>tangle_nodes_in_rank n \<and> (x,y)\<in>E)"
        {
          fix x
          assume "x\<in>new_player_nodes"
          hence "target x\<in>tangle_nodes_in_rank n" "(x,target x)\<in>E"
            unfolding new_player_nodes_def
            apply simp_all
            using some_eq_imp[of _ "target x"]
            unfolding target_def by blast+
        } note target=this

        have target_eq: "x\<in>new_player_nodes \<longleftrightarrow>
             (x\<in>tangle_nodes_in_rank (Suc n) \<and> x\<in>V\<^sub>\<alpha> \<and> x\<notin>tangle_nodes_in_rank n \<and>
             target x\<in>tangle_nodes_in_rank n \<and> (x,target x)\<in>E)" for x
          unfolding new_player_nodes_def
          apply (rule iffI; simp)
          using some_eq_imp[of _ "target x"]
          unfolding target_def by blast+

        define \<sigma>' where "\<sigma>' = (\<lambda>x. if x \<in> new_player_nodes - \<Union>new_tangles then Some (target x) else None)"
        have \<sigma>'_strat: "strategy_of V\<^sub>\<alpha> \<sigma>'"
          unfolding strategy_of_def E_of_strat_def \<sigma>'_def
          by (auto simp: target_eq split: if_splits)

        have \<sigma>'_dom: "dom \<sigma>' = new_player_nodes - \<Union>new_tangles"
          unfolding \<sigma>'_def by (auto split: if_splits)

        have \<sigma>'_ran: "ran \<sigma>' \<subseteq> tangle_nodes_in_rank n"
          unfolding \<sigma>'_def ran_def by (auto simp: target_eq)

        have new_tangles_in_T: "\<forall>t\<in>new_tangles. t\<in>T"
          unfolding new_tangles_def by blast

        hence new_tangles_tangles: "\<forall>t\<in>new_tangles. player_tangle t"
          using tangles_T by fast

        from new_tangles_in_T have fin_new_tangles: "finite new_tangles"
          using finite_subset[OF _ finite_T] by fast

        have "\<forall>t1\<in>new_tangles. \<forall>t2\<in>new_tangles. \<forall>v\<in>opponent_escapes t1. v\<notin>t2"
          unfolding new_tangles_def by fast

        from combined_tangle_strat[OF fin_new_tangles new_tangles_tangles this]
        obtain \<sigma>'' where
          \<sigma>''_strat: "strategy_of V\<^sub>\<alpha> \<sigma>''" and
          \<sigma>''_dom: "dom \<sigma>'' = \<Union>new_tangles \<inter> V\<^sub>\<alpha>" and
          \<sigma>''_ran: "ran \<sigma>'' \<subseteq> \<Union>new_tangles" and
          \<sigma>''_winning: "\<forall>v\<in>\<Union>new_tangles.
            \<forall>xs. cycle_node (player_tangle_subgraph (\<Union>new_tangles) \<sigma>'') v xs \<longrightarrow> winning_player xs"
          by auto

        from \<sigma>_dom \<sigma>'_dom \<sigma>''_dom have \<tau>_doms_disj:
          "dom \<sigma> \<inter> dom \<sigma>' = {}"
          "dom \<sigma> \<inter> dom \<sigma>'' = {}"
          "dom \<sigma>' \<inter> dom \<sigma>'' = {}"
          unfolding new_player_nodes_def new_tangles_def
          by auto

        define \<tau> where "\<tau> = \<sigma> ++ \<sigma>' ++ \<sigma>''"

        from \<sigma>_strat \<sigma>'_strat \<sigma>''_strat have \<tau>_strat: "strategy_of V\<^sub>\<alpha> \<tau>"
          unfolding \<tau>_def by auto

        from \<sigma>_dom \<sigma>'_dom \<sigma>''_dom \<tau>_strat have \<tau>_dom: "dom \<tau> = V\<^sub>\<alpha> \<inter> (tangle_nodes_in_rank (Suc n) - A)"
          unfolding \<tau>_def strategy_of_def new_player_nodes_def new_tangles_def
          sorry, xxx sorry

        have \<tau>_ran: "ran \<tau> \<subseteq> tangle_nodes_in_rank (Suc n)"
        proof (rule subsetI)
          fix y assume y_in_ran_\<tau>: "y \<in> ran \<tau>"
          with \<tau>_dom obtain x where
            \<tau>_x_y: "\<tau> x = Some y" and
            x_in_dom: "x \<in> dom \<tau>"
            unfolding ran_def by blast

          from x_in_dom consider (\<sigma>) "x \<in> dom \<sigma>" | (\<sigma>') "x \<in> dom \<sigma>'" | (\<sigma>'') "x \<in> dom \<sigma>''"
            unfolding \<tau>_def by fast
          thus "y \<in> tangle_nodes_in_rank (Suc n)" proof cases
            case \<sigma>
            with \<tau>_x_y \<tau>_doms_disj have "\<sigma> x = Some y"
              unfolding \<tau>_def by blast
            from ranI[of \<sigma>, OF this] \<sigma>_ran show ?thesis
              using tangle_nodes_in_rank_mono by auto
          next
            case \<sigma>'
            with \<tau>_x_y \<tau>_doms_disj have "\<sigma>' x = Some y"
              unfolding \<tau>_def by blast
            from ranI[of \<sigma>', OF this] \<sigma>'_ran show ?thesis
              using nodes_in_rank_mono by auto
          next
            case \<sigma>''
            with \<tau>_x_y \<tau>_doms_disj have "\<sigma>'' x = Some y"
              unfolding \<tau>_def by blast
            from ranI[of \<sigma>'', OF this] \<sigma>''_ran show ?thesis
              unfolding new_tangles_def
              using nodes_in_rank_mono by blast
          qed
        qed

        have \<tau>_closed_rank:
          "\<forall>m. \<forall>x\<in>tangle_nodes_in_rank m - A. \<forall>y\<in>induced_subgraph V\<^sub>\<alpha> \<tau> `` {x}. y \<in> tangle_nodes_in_rank m"
        proof (intro allI ballI)
          fix m x y
          assume x_in_m_minus_A:"x \<in> tangle_nodes_in_rank m - A" and
                 y_succ_x: "y \<in> induced_subgraph V\<^sub>\<alpha> \<tau> `` {x}"
          hence x_in_m: "x \<in> tangle_nodes_in_rank m" and
                x_notin_A: "x \<notin> A" and
                edge_in_E: "(x,y)\<in>E"
            by auto
          show "y \<in> tangle_nodes_in_rank m"
          proof (cases "x\<in>V\<^sub>\<alpha>")
            case True
            with y_succ_x have \<tau>_x_y: "\<tau> x = Some y"
              unfolding induced_subgraph_def
              by (simp add: edge_in_E_of_strat)
            then consider (\<sigma>) "x \<in> dom \<sigma>" | (\<sigma>') "x \<in> dom \<sigma>'" |  (\<sigma>'') "x \<in> dom \<sigma>''"
              unfolding \<tau>_def by blast
            thus ?thesis proof cases
              case \<sigma>
              with \<tau>_x_y \<tau>_doms_disj have "\<sigma> x = Some y"
                unfolding \<tau>_def by blast
              with edge_in_E have "(x,y)\<in>induced_subgraph V\<^sub>\<alpha> \<sigma>"
                unfolding induced_subgraph_def
                by (simp add: edge_in_E_of_strat)

              with \<sigma>_closed_rank x_in_m_minus_A show ?thesis by blast

            next
              case \<sigma>'

              with \<tau>_x_y \<tau>_doms_disj have "\<sigma>' x = Some y"
                unfolding \<tau>_def by blast
              with \<sigma>'_ran have y_in_n: "y \<in> tangle_nodes_in_rank n"
                using ranI by fast

              from \<sigma>' \<sigma>'_dom have "x \<in> new_player_nodes" by fast

              with x_in_m y_in_n show ?thesis
                unfolding \<sigma>'_def
                using target_eq[of x] in_mono[OF tangle_nodes_in_rank_mono] nat_le_linear
                by blast

            next
              case \<sigma>''

              with \<tau>_x_y \<tau>_doms_disj have "\<sigma>'' x = Some y"
                unfolding \<tau>_def by blast
              with ranI[of \<sigma>'', OF this] \<sigma>''_ran have y_in_Suc_n: "y \<in> tangle_nodes_in_rank (Suc n)"
                unfolding new_tangles_def by blast

              from \<sigma>'' \<sigma>''_dom have "x \<in> \<Union>new_tangles \<inter> V\<^sub>\<alpha>" by fast

              with x_in_m show ?thesis
                unfolding new_tangles_def
                using in_mono[OF tangle_nodes_in_rank_mono] not_less_eq_eq[of m n] y_in_Suc_n
                by blast
            qed
          next
            case False thus ?thesis
              using tangle_nodes_in_rank_edges_same[OF x_in_m x_notin_A edge_in_E] by simp
          qed
        qed

        have \<tau>_forces_A_or_wins:
          "\<forall>x\<in>tangle_nodes_in_rank (Suc n). \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<tau>) x xs ys
              \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
        proof (intro ballI allI impI)
          fix x xs ys
          assume x_in_Suc_n: "x \<in> tangle_nodes_in_rank (Suc n)" and
                lasso_x_xs_ys: "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<tau>) x xs ys"
          then obtain y where
            path_x_xs_y: "path (induced_subgraph V\<^sub>\<alpha> \<tau>) x xs y" and
            cycle_y_ys: "cycle_node (induced_subgraph V\<^sub>\<alpha> \<tau>) y ys" and
            y_in_ys: "y \<in> set ys"
            unfolding lasso_from_node_def
            using origin_in_cycle_node by fast

          consider (has_A) "set (xs@ys) \<inter> A \<noteq> {}" | (no_A) "set (xs@ys) \<inter> A = {}" by blast
          thus "set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys" proof cases
            case has_A thus ?thesis by blast
          next
            case no_A
            hence no_A_xs: "set xs \<inter> A = {}" and no_A_ys: "set ys \<inter> A = {}" by auto
            with x_in_Suc_n lasso_x_xs_ys
            have x_in_Suc_n_min_A: "x \<in> tangle_nodes_in_rank (Suc n) - A"
              using origin_in_lasso by fastforce

            consider (stays_in_Suc) "set (xs@ys) \<inter> tangle_nodes_in_rank n = {}" |
                     (leaves) "set (xs@ys) \<inter> tangle_nodes_in_rank n \<noteq> {}" by blast
            thus ?thesis proof cases
              case stays_in_Suc

              from path_partially_closed_dest[OF x_in_Suc_n_min_A _ path_x_xs_y no_A_xs] \<tau>_closed_rank
                   origin_in_cycle_node[OF cycle_y_ys] no_A_ys
              have y_in_Suc_n_min_A: "y \<in> tangle_nodes_in_rank (Suc n) - A" by blast
              hence y_in_Suc: "y \<in> tangle_nodes_in_rank (Suc n)" by blast
              thus ?thesis proof (cases rule: tangle_nodes_in_rank_Suc_cases)
                case base with y_in_ys stays_in_Suc show ?thesis by auto
              next
                (** This case seems to not actually be helpful here because it cannot be guaranteed
                    that it is not also in one of the new tangles *)
                case own
                show ?thesis sorry, xxx sorry
              next
                case opponent
                from cycle_node_D[OF cycle_y_ys] obtain y' where
                  edge_in_subgraph: "(y,y')\<in>induced_subgraph V\<^sub>\<alpha> \<tau>" and y'_in_ys: "y' \<in> set ys"
                  by blast
                with opponent have y'_in_n: "y' \<in> tangle_nodes_in_rank n" by simp
                with stays_in_Suc y'_in_ys show ?thesis by auto
              next
                (** This case isn't actually useful here, because there is no telling whether it's
                    in one of the actual new tangles. Some refinement of the definition in this
                    proof might be needed. *)
                case escape
                from y_in_Suc stays_in_Suc y_in_ys have y_in_new_nodes: "y \<in> ?new_nodes" by force
                with escape have "y \<in> \<Union>new_tangles" sorry
                show ?thesis sorry, xxx sorry
              qed

            next
              case leaves

              from \<sigma>_dom \<tau>_dom \<tau>_doms_disj(2) \<sigma>'_dom target_eq
              have subset:
                "induced_subgraph V\<^sub>\<alpha> \<tau> \<inter> (tangle_nodes_in_rank n - A) \<times> (tangle_nodes_in_rank n - A)
                  \<subseteq> induced_subgraph V\<^sub>\<alpha> \<sigma>"
                unfolding \<tau>_def induced_subgraph_def E_of_strat_def
                apply safe
                apply simp_all
                  subgoal by blast
                  subgoal by auto
                done

              from leaves no_A obtain v where
                v_in_xs_ys: "v \<in> set (xs@ys)" and
                v_in_n_min_A: "v \<in> tangle_nodes_in_rank n - A"
                by blast

              then consider (v_xs) "v \<in> set xs" | (v_ys) "v \<in> set ys" by fastforce
              thus ?thesis proof cases
                case v_xs
                from no_A_xs path_intermediate_node[OF path_x_xs_y v_xs] obtain xs' where
                  xs'_in_xs: "set xs' \<subseteq> set xs" and
                  no_A_xs': "set xs' \<inter> A = {}" and
                  path_v_xs'_y: "path (induced_subgraph V\<^sub>\<alpha> \<tau>) v xs' y"
                  by fastforce

                from path_partially_closed_set[OF v_in_n_min_A _ path_v_xs'_y no_A_xs'] \<tau>_closed_rank
                have xs_in_n_min_A: "set xs' \<subseteq> tangle_nodes_in_rank n - A" by blast

                from path_partially_closed_dest[OF v_in_n_min_A _ path_v_xs'_y no_A_xs'] \<tau>_closed_rank no_A_ys
                have y_in_n_min_A: "y \<in> tangle_nodes_in_rank n - A"
                  using origin_in_cycle_node[OF cycle_y_ys] by auto

                from cycle_partially_closed_set[OF y_in_n_min_A _ cycle_y_ys no_A_ys] \<tau>_closed_rank
                have ys_in_n_min_A: "set ys \<subseteq> tangle_nodes_in_rank n - A" by blast

                from subgraph_path[OF subset path_restr_V[OF path_v_xs'_y xs_in_n_min_A y_in_n_min_A]]
                     subgraph_cycle[OF subset cycle_restr_V[OF cycle_y_ys ys_in_n_min_A]]
                have "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) v xs' ys"
                  unfolding lasso_from_node_def by blast
                with v_in_n_min_A \<sigma>_forces_A_or_wins no_A_xs' show ?thesis by fastforce
              next
                case v_ys
                from cycle_node_intermadiate_node[OF cycle_y_ys v_ys] no_A_ys
                obtain ys' where
                  ys'_set_ys[simp]: "set ys' = set ys" and
                  no_A_ys': "set ys' \<inter> A = {}" and
                  cycle_v_ys': "cycle_node (induced_subgraph V\<^sub>\<alpha> \<tau>) v ys'"
                  by blast

                from cycle_partially_closed_set[OF v_in_n_min_A _ cycle_v_ys' no_A_ys'] \<tau>_closed_rank
                have ys_in_n_min_A: "set ys \<subseteq> tangle_nodes_in_rank n - A" by auto
                with cycle_y_ys have y_in_n_min_A: "y \<in> tangle_nodes_in_rank n - A"
                  using origin_in_cycle_node by fast

                from subgraph_cycle[OF subset cycle_restr_V[OF cycle_y_ys ys_in_n_min_A]]
                have "lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) y [] ys"
                  by (simp add: cycle_node_iff_loop loop_impl_lasso)
                with y_in_n_min_A \<sigma>_forces_A_or_wins no_A_ys show ?thesis by auto
              qed
            qed
          qed
        qed

        show ?case
          apply (rule exI[where x="\<tau>"]; intro conjI)
            subgoal using \<tau>_strat .
            subgoal using \<tau>_dom .
            subgoal using \<tau>_ran .
            subgoal using \<tau>_closed_rank .
            subgoal using \<tau>_forces_A_or_wins .
          done
      qed
    end

    lemma tangle_nodes_in_rank_ss: "tangle_nodes_in_rank A n \<subseteq> A \<union> V"
      apply (induction n; simp)
      using V\<^sub>\<alpha>_subset tangles_T
      unfolding player_tangle_def by auto

    lemma tangle_nodes_in_rank_finite[simp, intro!]: "finite A \<Longrightarrow> finite (tangle_nodes_in_rank A n)"
      using fin_V finite_Un[of A V] finite_subset[OF tangle_nodes_in_rank_ss, of A n] by simp

    lemma player_tangle_attractor_ss: "player_tangle_attractor A \<subseteq> A \<union> V"
      using player_tangle_attractor_ss_tangle_nodes_in_rank tangle_nodes_in_rank_ss by blast

    lemma finite_player_tangle_attractor: "finite (player_tangle_attractor A - A)"
      using player_tangle_attractor_ss[of A] Diff_subset_conv[of "player_tangle_attractor A" A V]
      using rev_finite_subset[OF fin_V]
      by simp

    lemma player_tangle_attractor_max_rank_eq:
    "\<exists>n. player_tangle_attractor A = tangle_nodes_in_rank A n"
    proof -
      have 1: "\<Union>(range (tangle_nodes_in_rank A)) - A = \<Union>(range (\<lambda>x. tangle_nodes_in_rank A x - A))"
        by auto

      have "\<exists>n. player_tangle_attractor A - A = tangle_nodes_in_rank A n - A"
        using finite_player_tangle_attractor
        unfolding player_tangle_attractor_eq_tangle_nodes_in_rank
        apply (subst 1)
        apply (rule finite_union_nat_range_bound)
          subgoal by simp
          subgoal by (simp add: Diff_mono tangle_nodes_in_rank_mono)
        done

      thus ?thesis
        using player_tangle_attractor_subset[of A] tangle_nodes_in_rank_subset[of A]
        using Diff_partition[of A "player_tangle_attractor A"]
        by blast
    qed

    lemma player_tangle_attractor_forces_A_or_wins: "\<exists>\<sigma>.
        strategy_of V\<^sub>\<alpha> \<sigma>
        \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> (player_tangle_attractor A - A) \<and> ran \<sigma> \<subseteq> player_tangle_attractor A
        \<and> (\<forall>x \<in> player_tangle_attractor A - A. \<forall>y. (x,y) \<in> induced_subgraph V\<^sub>\<alpha> \<sigma> \<longrightarrow> y \<in> player_tangle_attractor A)
        \<and> (\<forall>x \<in> player_tangle_attractor A. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
              \<longrightarrow> (set (xs@ys) \<inter> A \<noteq> {} \<or> winning_player ys))"
    proof -
      obtain n where attr_A_rank_n: "player_tangle_attractor A = tangle_nodes_in_rank A n"
        using player_tangle_attractor_max_rank_eq by blast

      from tangle_nodes_in_rank_forces_A_or_wins[of A n] obtain \<sigma> where
        \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>" and
        \<sigma>_dom: "dom \<sigma> = V\<^sub>\<alpha> \<inter> (tangle_nodes_in_rank A n - A)" and
        \<sigma>_ran: "ran \<sigma> \<subseteq> tangle_nodes_in_rank A n" and
        \<sigma>_closed: "\<forall>m. \<forall>x\<in>tangle_nodes_in_rank A m - A. \<forall>y\<in>induced_subgraph V\<^sub>\<alpha> \<sigma> `` {x}. y \<in> tangle_nodes_in_rank A m" and
        \<sigma>_forces_A_or_wins: "\<forall>x\<in>tangle_nodes_in_rank A n. \<forall>xs ys. lasso_from_node (induced_subgraph V\<^sub>\<alpha> \<sigma>) x xs ys
          \<longrightarrow> set (xs @ ys) \<inter> A \<noteq> {} \<or> winning_player ys"
        by auto

      show ?thesis
        apply (rule exI[where x="\<sigma>"]; intro conjI)
          subgoal by fact
          subgoal using \<sigma>_dom attr_A_rank_n by simp
          subgoal using \<sigma>_ran attr_A_rank_n by simp
          subgoal using \<sigma>_closed attr_A_rank_n by simp
          subgoal using \<sigma>_forces_A_or_wins attr_A_rank_n by simp
        done
    qed
  end
end

end