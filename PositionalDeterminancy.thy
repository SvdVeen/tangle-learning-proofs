theory PositionalDeterminancy
imports Main Attractors WinningRegions
begin

(** We use a proof for positional determinancy to check our definitions. *)
chapter \<open>Positional Determinancy\<close>
section \<open>Auxiliary Lemmas\<close>
context paritygame begin
(** If we remove a maximal attractor from a game, the remainder is a valid parity game. *)
lemma attractor_subgame:
  assumes "X = attractor \<alpha> A"
  assumes "E' = Restr E (V-X)"
  assumes "V' = V-X"
  assumes "V\<^sub>0' = V\<^sub>0-X"
  shows "paritygame E' V' V\<^sub>0'"
  using V\<^sub>0_in_V Int_Diff[of V\<^sub>0 V X] remove_attractor_subgame
  by (simp add: assms Int_absorb1 Int_absorb2)

(** If we remove some set from a game and the result is a valid subgame, then its player nodes
    are a subset of the player nodes in the whole game. *)
lemma subgame_V_player_subset:
  assumes "paritygame E' V' V\<^sub>0'"
  assumes "V' = V-S"
  assumes "V\<^sub>0' = V\<^sub>0-S"
  shows "paritygame.V_player V' V\<^sub>0' \<alpha> \<subseteq> V_player \<alpha>"
  using assms arena.V\<^sub>1_def paritygame.axioms
  apply (cases \<alpha>; simp add: paritygame.V_player.simps V\<^sub>1_def)
  by fastforce

lemma subgame_V_opponent_subset:
  assumes "paritygame E' V' V\<^sub>0'"
  assumes V': "V' = V-S"
  assumes V\<^sub>0': "V\<^sub>0' = V\<^sub>0-S"
  shows "paritygame.V_opponent V' V\<^sub>0' \<alpha> \<subseteq> V_opponent \<alpha>"
  using assms arena.V\<^sub>1_def paritygame.axioms
  apply (cases \<alpha>; simp add: paritygame.V_opponent.simps V\<^sub>1_def)
  by fastforce

(** The strategy of a player in a subgame game is also a strategy of that player in the whole
    game if this game is a subset created by taking out some set from the game. *)
lemma subgame_strategy_of_V_player:
  assumes subgame: "paritygame E' V' V\<^sub>0'"
  assumes E'_subset_E: "E' \<subseteq> E"
  assumes V'_def: "V' = V-S"
  assumes V\<^sub>0'_def: "V\<^sub>0' = V\<^sub>0-S"
  shows "arena.strategy_of E' (paritygame.V_player V' V\<^sub>0' \<alpha>) \<sigma>
    \<Longrightarrow> strategy_of (V_player \<alpha>) \<sigma>"
  using E'_subset_E subgame_V_player_subset[OF subgame V'_def V\<^sub>0'_def]
  unfolding strategy_of_def arena.strategy_of_def[OF paritygame.axioms[OF subgame]]
  by fast

(** If a subgame was taken by removing an attractor from the whole game, then any winning regions
    in that subgame are also winning regions in the whole game. *)
lemma attractor_subgame_winning_region:
  assumes "paritygame E' V' V\<^sub>0'"
  assumes E'_def: "E' = E \<inter> (V-A)\<times>(V-A)"
  assumes V'_def: "V' = V-A"
  assumes V\<^sub>0'_def: "V\<^sub>0' = V\<^sub>0-A"
  assumes W_in_V': "W \<subseteq> V'"
  assumes A_def: "A = attractor (opponent \<alpha>) X"
  assumes W_winning_subgame: "paritygame.winning_region E' V' V\<^sub>0' pr \<alpha> W"
  shows "winning_region \<alpha> W"
proof -
  interpret subgame: paritygame E' V' V\<^sub>0' by fact
  from W_in_V' V'_def have W_in_V: "W \<subseteq> V" by auto
  from subgame_V_opponent_subset[OF subgame.paritygame_axioms V'_def V\<^sub>0'_def]
  have V_opponent_subset: "subgame.V_opponent \<alpha> \<subseteq> V_opponent \<alpha>" .

  from W_winning_subgame obtain \<sigma> where
        \<sigma>_strat_subgame: "subgame.strategy_of_player \<alpha> \<sigma>"
    and \<sigma>_dom_subgame: "dom \<sigma> = subgame.V_player \<alpha> \<inter> W"
    and \<sigma>_ran: "ran \<sigma> \<subseteq> W"
    and \<sigma>_winning_subgame: "\<forall>w\<in>W. \<forall>ys. reachable_cycle (subgame.induced_subgraph \<sigma>) w ys
      \<longrightarrow> player_wins_list \<alpha> ys"
    and \<sigma>_closed_opp_subgame: "E' `` (W\<inter>subgame.V_opponent \<alpha>) \<subseteq> W"
    using subgame.winning_region_strat by auto

  let ?G\<sigma> = "induced_subgraph \<sigma>"

  from \<sigma>_strat_subgame E'_def have \<sigma>_strat: "strategy_of_player \<alpha> \<sigma>"
    unfolding strategy_of_player_def subgame.strategy_of_player_def
    using subgame_strategy_of_V_player[OF subgame.paritygame_axioms _ V'_def V\<^sub>0'_def] by simp

  from \<sigma>_dom_subgame have \<sigma>_dom: "dom \<sigma> = V_player \<alpha> \<inter> W"
    using V\<^sub>1_def subgame.V\<^sub>1_def V'_def V\<^sub>0'_def subgame.V_player.simps W_in_V'
    by (cases \<alpha>) auto

  have \<sigma>_closed: "?G\<sigma> `` W \<subseteq> W"
  proof clarsimp
    fix w w'
    assume w_in_W: "w\<in>W" and edge_in_subgraph: "(w,w')\<in>?G\<sigma>"
    with W_in_V consider (w_player) "w\<in>V_player \<alpha>" | (w_opp) "w\<in>V_opponent \<alpha>"
      using v_notin_V_player_in_V_opponent by blast
    thus "w'\<in>W" proof cases
      case w_player
      with \<sigma>_dom \<sigma>_ran edge_in_subgraph w_in_W show ?thesis
        using ind_subgraph_edge_dst by auto
    next
      case w_opp
      hence w_opp': "w\<in>V_player (opponent \<alpha>)" using V_player_opponent by simp

      have edge_in_E': "(w,w')\<in>E'"
      proof -
        from edge_in_subgraph have edge_in_E: "(w,w')\<in>E" using ind_subgraph by blast
        moreover from w_in_W W_in_V' have w_notin_A: "w\<notin>A" unfolding V'_def by blast
        moreover from attractor_max_player[OF w_opp'] w_notin_A edge_in_E
        have w'_notin_A: "w'\<notin>A" unfolding V'_def A_def by blast
        ultimately show ?thesis using E'_def E_in_V by auto
      qed

      from w_opp \<sigma>_dom have "w \<notin> dom \<sigma>"
        by (cases \<alpha>; simp add: V\<^sub>1_def)
      from \<sigma>_closed_opp_subgame w_in_W subgame.ind_subgraph_notin_dom[OF edge_in_E' this]
           V'_def V\<^sub>0'_def W_in_V'
      have \<sigma>_closed_opp: "\<forall>w\<in>W. w \<in> V_opponent \<alpha> \<longrightarrow> E' `` {w} \<subseteq> W"
        using V\<^sub>1_def subgame.V\<^sub>1_def subgame.V_opponent.simps
        by (cases \<alpha>) auto

      from \<sigma>_closed_opp edge_in_E' w_in_W w_opp show ?thesis by blast
    qed
  qed

  from \<sigma>_closed \<sigma>_dom have W_closed_opp: "E `` (W \<inter> V_opponent \<alpha>) \<subseteq> W"
    using ind_subgraph_notin_dom
    by (cases \<alpha>; clarsimp simp add: V\<^sub>1_def) blast+

  have \<sigma>_winning: "\<forall>w\<in>W. \<forall>ys. reachable_cycle ?G\<sigma> w ys \<longrightarrow> player_wins_list \<alpha> ys"
  proof (rule ballI; rule allI; rule impI)
    fix w ys
    assume w_in_W: "w\<in>W" and reachable_cycle:
      "reachable_cycle ?G\<sigma> w ys"
    hence ys_notempty: "ys\<noteq>[]" by auto

    from reachable_cycle_closed_set[OF w_in_W \<sigma>_closed reachable_cycle]
    have ys_in_W: "set ys \<subseteq> W" .
    with reachable_cycle ys_in_W obtain w' where
      cycle: "cycle ?G\<sigma> w' ys" and w'_in_W: "w' \<in> W"
      unfolding reachable_cycle_def
      using origin_in_cycle by fast

    have "Restr ?G\<sigma> W \<subseteq> subgame.induced_subgraph \<sigma>"
      using ind_subgraph_restr_subarena[OF subgame.arena_axioms, of \<sigma>]
      using W_in_V' unfolding V'_def E'_def by auto
    from subgraph_cycle[OF this cycle_restr_V[OF cycle ys_in_W]]
    have "reachable_cycle (subgame.induced_subgraph \<sigma>) w' ys"
      using cycle_impl_reachable_cycle by fast

    with \<sigma>_winning_subgame w'_in_W
    show "player_wins_list \<alpha> ys" by blast
  qed

  from W_in_V W_closed_opp \<sigma>_strat \<sigma>_dom \<sigma>_ran \<sigma>_winning show ?thesis
    by (auto simp: winning_region_strat)
qed
end (** End of context paritygame. *)


section \<open>Maximal Winning Regions\<close>

(** In a parity game, there are two disjoint winning regions, one for each player.
    We will prove this by following a proof adapted from Zielonka's proof of positional
    determinancy. *)
lemma maximal_winning_regions:
  fixes V :: "'v set"
  assumes "paritygame E V V\<^sub>0"
  shows "\<exists>W\<^sub>0 W\<^sub>1. V = W\<^sub>0 \<union> W\<^sub>1 \<and> W\<^sub>0 \<inter> W\<^sub>1 = {}
    \<and> paritygame.winning_region E V V\<^sub>0 pr EVEN W\<^sub>0
    \<and> paritygame.winning_region E V V\<^sub>0 pr ODD W\<^sub>1"
proof -
  (** We must first show that V is finite before we can do our induction.
      This is required by the induction rule finite_psubset_induct. *)
  have "finite V" proof -
    interpret paritygame E V V\<^sub>0 by fact
    show ?thesis by blast
  qed

  (** We do an induction on the size of the game. *)
  thus ?thesis using assms
  proof (induction arbitrary: E V\<^sub>0 rule: finite_psubset_induct)
    case (psubset V)
    interpret paritygame E V V\<^sub>0 by fact

    (** We must consider an empty game as well as a nonempty game. *)
    consider (V_empty) "V = {}" | (V_notempty) "V \<noteq> {}" by fast
    thus ?case proof cases
      (** In an empty game, the two winning regions are empty sets. *)
      case V_empty thus ?thesis
        using winning_region_empty by auto

    next
      case V_notempty

      (** We get the top priority p in V*)
      define p where "p = pr_set V"

      (** We get the player who wins priority p *)
      then obtain \<alpha> where "\<alpha> = player_wins_pr p" by simp
      hence player_wins_p: "player_winningP \<alpha> p"
        by (cases \<alpha>; simp add: player_wins_pr_def split: if_splits)
      (** Shorthand for later. *)
      let ?V\<^sub>\<alpha> = "V_player \<alpha>"
      let ?\<beta> = "opponent \<alpha>"
      let ?V\<^sub>\<beta> = "V_opponent \<alpha>"

      (** We take some v in V of priority p. *)
      obtain v where "v\<in>V" and v_pr: "pr v = p"
        using pr_V_exists[OF \<open>V\<noteq>{}\<close>] p_def by blast

      (** We attract to that v for \<alpha> *)
      define A where "A = attractor \<alpha> {v}"
      with \<open>v\<in>V\<close> have "v \<in> A" using attractor_subset by blast

      (** Removing an attractor from a game yields a valid subgame. *)
      interpret subgame: paritygame "Restr E (V-A)" "V-A" "V\<^sub>0-A"
        using attractor_subgame[OF A_def] by blast

      (** By our IH, we now have two disjoint maximal winning regions in this subgame, W\<^sub>\<alpha> and W\<^sub>\<beta>. *)
      from \<open>v\<in>A\<close> \<open>v\<in>V\<close> have "V-A \<subset> V" by blast
      from psubset.IH[OF this subgame.paritygame_axioms]
      obtain W\<^sub>\<alpha> W\<^sub>\<beta> where
        W_comp: "V-A = W\<^sub>\<alpha> \<union> W\<^sub>\<beta>" and
        W_disj: "W\<^sub>\<alpha> \<inter> W\<^sub>\<beta> = {}" and
        W\<^sub>\<alpha>_win: "subgame.winning_region \<alpha> W\<^sub>\<alpha>" and
        W\<^sub>\<beta>_win: "subgame.winning_region ?\<beta> W\<^sub>\<beta>"
        using opponent.simps(2) apply (cases \<alpha>)
        by fastforce (metis Int_commute Un_commute)

      (** W\<^sub>\<beta> might be empty, so we need to account for that case. *)
      consider (W\<^sub>\<beta>_empty) "W\<^sub>\<beta> = {}" | (W\<^sub>\<beta>_notempty) "W\<^sub>\<beta> \<noteq> {}" by blast
      thus ?thesis proof cases
        case W\<^sub>\<beta>_empty
        (** The whole game now consists of W\<^sub>\<alpha> and A. *)
        with \<open>v\<in>V\<close> W_comp A_def have V_comp: "V = W\<^sub>\<alpha> \<union> A"
          using attractor_subset_graph[of "{v}"] by blast

        (** The entire game should now be won by \<alpha>. *)
        moreover have "winning_region \<alpha> (W\<^sub>\<alpha>\<union>A)"
        proof -
          (** We take the winning strategy for W\<^sub>\<alpha>. *)
          from W\<^sub>\<alpha>_win obtain \<sigma> where
            \<sigma>_strat: "subgame.strategy_of_player \<alpha> \<sigma>" and
            \<sigma>_dom: "dom \<sigma> = subgame.V_player \<alpha> \<inter> W\<^sub>\<alpha>" and
            \<sigma>_ran: "ran \<sigma> \<subseteq> W\<^sub>\<alpha>" and
            \<sigma>_winning:
              "\<forall>w\<in>W\<^sub>\<alpha>. \<forall>xs. reachable_cycle (subgame.induced_subgraph \<sigma>) w xs
                \<longrightarrow> subgame.player_wins_list \<alpha> xs"
            unfolding subgame.winning_region_strat by auto

          (** We also take the attractor strategy for A. *)
          from A_def obtain \<sigma>' where
            \<sigma>'_strat: "strategy_of ?V\<^sub>\<alpha> \<sigma>'" and
            \<sigma>'_dom: "dom \<sigma>' = (A-{v}) \<inter> ?V\<^sub>\<alpha>" and
            \<sigma>'_ran: "ran \<sigma>' \<subseteq> A" and
            \<sigma>'_closed: "\<forall>v\<in>A-{v}. \<forall>v'. (v,v') \<in> induced_subgraph \<sigma>' \<longrightarrow> v' \<in> A" and
            \<sigma>'_forces_v: "\<forall>a\<in>A. \<forall>xs. lasso' (induced_subgraph \<sigma>') a xs \<longrightarrow> set xs \<inter> {v} \<noteq> {}"
            using attractor_attracts[of \<alpha> "{v}"] by blast

          (** If v belongs to the player, we need to assign it a successor to complete our
              strategy. We do this with v_choice, which assigns a random valid successor.*)
          define v_target where "v_target \<equiv> SOME v'. v' \<in> E `` {v}"
          with \<open>v\<in>V\<close> have v_target_edge: "(v,v_target)\<in>E"
            using succ some_in_eq[of "E `` {v}"] by blast

          (** If v belongs to \<alpha>, v_choice is a strategy that assigns it a random successor.
              Otherwise, v_choice is an empty strategy. *)
          define v_choice where "v_choice \<equiv> if v \<in> ?V\<^sub>\<alpha> then [v\<mapsto>v_target] else Map.empty"

          (** The domain of v_choice depends on who owns v. *)
          have v_choice_dom:
            "v\<in>?V\<^sub>\<alpha> \<longrightarrow> dom v_choice = {v}"
            "v\<notin>?V\<^sub>\<alpha> \<longrightarrow> dom v_choice = {}"
            unfolding v_choice_def by auto

          (** v_choice is a valid strategy for \<alpha>. *)
          from v_choice_dom v_target_edge
          have v_choice_strat: "strategy_of_player \<alpha> v_choice"
            unfolding v_choice_def strategy_of_player_def
            using strategy_of_overwrite
            by (cases \<alpha>; simp add: V\<^sub>1_def)

          (** The range of v_choice lies in V. *)
          from \<open>v\<in>V\<close> v_target_edge have v_choice_ran: "ran v_choice \<subseteq> V"
            unfolding v_choice_def using E_in_V by auto

          (** We combine our three strategies to get the winning strategy for \<alpha>. *)
          let ?\<tau> = "\<sigma> ++ \<sigma>' ++ v_choice"
          let ?G\<tau> = "induced_subgraph ?\<tau>"

          (** \<tau> is a valid strategy for \<alpha> because it combines three valid strategies for \<alpha>. *)
          from \<sigma>_strat \<sigma>'_strat v_choice_strat
          have \<tau>_strat: "strategy_of_player \<alpha> ?\<tau>"
            unfolding strategy_of_player_def subgame.strategy_of_player_def
            unfolding strategy_of_def subgame.strategy_of_def
            unfolding E_of_strat_def
            by (cases \<alpha>; simp add: V\<^sub>1_def subgame.V\<^sub>1_def) blast+

          (** The domain of \<tau> covers all \<alpha>-nodes in V, since the three domains collectively contain
              all of these nodes. *)
          moreover from \<sigma>_dom \<sigma>'_dom v_choice_dom have \<tau>_dom: "dom ?\<tau> = ?V\<^sub>\<alpha> \<inter> V"
            apply (cases \<alpha>; cases "v\<in>?V\<^sub>\<alpha>"; simp add: V\<^sub>1_def subgame.V\<^sub>1_def)
            using V_comp V\<^sub>0_in_V by auto

          (** The range of \<tau> lies in V because all three ranges lie in V. *)
          moreover from \<sigma>_ran \<sigma>'_ran v_choice_ran have \<tau>_ran: "ran ?\<tau> \<subseteq> V"
            using V_comp by (auto simp: ran_def)

          (** Trivially, V is closed in G[\<tau>] because V is the whole graph. *)
          moreover have \<tau>_closed: "?G\<tau> `` V \<subseteq> V"
            using E_closed_V ind_subgraph by blast

          (** Every reachable cycle in G[\<tau>] is won by \<alpha>. *)
          moreover
          {
            fix x ys
            assume x_in_V: "x \<in> V"
               and reachable_cycle: "reachable_cycle ?G\<tau> x ys"
            hence "ys\<noteq>[]" by auto
            (** Our reachable cycle can be split into a path and a cycle. *)
            from reachable_cycle obtain xs y where
              path: "path ?G\<tau> x xs y" and
              cycle: "cycle ?G\<tau> y ys" and
              y_in_ys: "y \<in> set ys"
              unfolding reachable_cycle_def
              using origin_in_cycle by fast
            (** Because V is closed, the whole cycle lies in V. *)
            hence "y\<in>V" and ys_in_V: "set ys \<subseteq> V"
              using ind_subgraph_path path_closed_V x_in_V
              using ind_subgraph_cycle cycle_in_V
              by blast+

            (** We must consider the possiblity that our cycle passes through A, and the
                possibility that it does not. *)
            consider (A_in_ys) "set ys \<inter> A \<noteq> {}" | (A_notin_ys) "set ys \<inter> A = {}" by blast
            hence "player_wins_list \<alpha> ys" proof cases
              (** In this case, we will prove that the cycle must pass through v, and because v is
                  the highest priority in V, which is won by \<alpha>, the cycle is won by \<alpha>. *)
              case A_in_ys
              have v_in_ys: "v \<in> set ys" proof (rule ccontr)
                assume "v \<notin> set ys"
                (** We start by getting the same cycle, but starting from a node in A.
                    Like ys, this cycle cannot be empty. *)
                from A_in_ys obtain y' where y'_in_ys: "y'\<in>set ys" and "y'\<in>A" by blast
                from cycle_intermediate_node[OF cycle y'_in_ys]
                obtain ys' where
                  sets_eq: "set ys' = set ys" and
                  cycle_y': "cycle ?G\<tau> y' ys'"
                  by blast
                from sets_eq \<open>ys\<noteq>[]\<close> have ys'_notempty: "ys'\<noteq>[]" by force

                have "lasso' (induced_subgraph \<sigma>') y' ys'"
                proof -
                  (** Because the cycle does not contain v, y' is part of A-{v}. *)
                  from \<open>v\<notin> set ys\<close> sets_eq \<open>y'\<in>A\<close>
                  have "y' \<in> A-{v}" and ys'_no_v: "set ys' \<inter> {v} = {}"
                    using origin_in_cycle[OF cycle_y'] by blast+

                  (** The region A is partially closed in A-{v} in G[\<tau>]. *)
                  {
                    fix x y assume assms: "x \<in> A-{v}" "(x,y) \<in> ?G\<tau>"
                    with \<sigma>_dom v_choice_dom have
                      "x \<notin> dom \<sigma>" "x \<notin> dom v_choice"
                      using W_comp by auto
                    with assms \<sigma>'_closed have "y \<in> A"
                      using ind_subgraph_add_notin_dom[of x y] by blast
                  }
                  (** This means the whole cycle is contained in A-{v}. *)
                  with cycle_partially_closed_set[OF \<open>y'\<in>A-{v}\<close> _ cycle_y' ys'_no_v]
                  have ys'_in_A_not_V: "set ys' \<subseteq> A-{v}" by blast

                  (** Within the region A-{v}, G[\<tau>] is a subgraph of G[\<sigma>']. *)
                  from \<sigma>'_dom v_choice_dom have
                    "Restr ?G\<tau> (A-{v}) \<subseteq> induced_subgraph \<sigma>'"
                    unfolding induced_subgraph_def E_of_strat_def by auto
                  (** The whole cycle is contained in A-{v}, and G[\<tau>] is a subgraph of G[\<sigma>'] in that
                      region, so this cycle exists in G[\<sigma>']. Furthermore, a cycle is just a lasso
                      without a spoke, so we have a lasso in G[\<sigma>'] from y with only the loop ys'.*)
                  from subgraph_cycle[OF this cycle_restr_V[OF cycle_y' ys'_in_A_not_V]]
                  show ?thesis
                    using cycle_iff_lasso lassos_equiv by fast
                qed
                (** Since this loop is forced to intersect with {v}, and it is the same loop as ys
                    with a different starting point, ys also has to contain v. *)
                with \<sigma>'_forces_v \<open>y'\<in>A\<close> \<open>v\<notin>set ys\<close> sets_eq
                show False by blast
              qed

              (** Since ys contains v, and this is the highest priority in V, which is won by \<alpha>,
                  the cycle ys is won by \<alpha>. *)
              from player_wins_p v_pr show ?thesis
                using pr_V_in_list[OF ys_in_V v_in_ys]
                by (simp add: p_def)

            next
              (** If our cycle does not contain A, the whole cycle must be part of W\<^sub>\<alpha>.
                  Cycles in W\<^sub>\<alpha> are won using the region's winning strategy, so it is won with \<tau>. *)
              case A_notin_ys
              with y_in_ys have "y \<notin> A" by blast
              from A_notin_ys y_in_ys have
                y_in_V': "y \<in> V-A" and ys_in_V': "set ys \<subseteq> V-A"
                using cycle_in_V[OF \<open>y\<in>V\<close> ind_subgraph_cycle[OF cycle]]
                by fast+

              (** Because the cycle is contained entirely in V-A, it also exists in the subgame's
                  G[\<sigma>]. *)
              have "reachable_cycle (subgame.induced_subgraph \<sigma>) y ys"
              proof -
                (** We show that G[\<tau>] is a subgraph of G[\<sigma>] in the region V-A. *)
                from \<open>v\<in>A\<close> \<sigma>'_dom v_choice_dom have
                  "Restr ?G\<tau> (V-A) \<subseteq> subgame.induced_subgraph \<sigma>"
                  unfolding induced_subgraph_def subgame.induced_subgraph_def
                  unfolding E_of_strat_def
                  apply (safe; clarsimp) by fastforce auto

                (** Because our cycle exists entirely within V-A, it also exists in G[\<sigma>] in the
                    subgame. *)
                from subgraph_cycle[OF this cycle_restr_V[OF cycle ys_in_V']]
                show ?thesis
                  by (simp add: cycle_impl_reachable_cycle)
              qed

              (** All reachable cycles from W\<^sub>\<alpha> that remain in the subgame are won by \<alpha> using the
                  strategy \<sigma>, so this cycle is also won in our combined strategy. *)
              with \<sigma>_winning y_in_V' \<open>y\<notin>A\<close> show ?thesis
                unfolding W_comp W\<^sub>\<beta>_empty by blast
            qed
          } note \<tau>_winning=this

          (** By the former properties combined, we now know that W\<^sub>\<alpha> \<union> A is won by \<alpha> with the
              winning strategy \<tau>. *)
          ultimately show ?thesis
            unfolding winning_region_strat
            using closed_ind_subgraph_opp[OF \<tau>_closed \<tau>_strat] V_comp
            by blast
        qed

        (** The whole game consists of only W\<^sub>\<alpha> \<union> A, so the winning region for \<beta> is the empty set. *)
        ultimately show ?thesis
          using winning_region_empty[of ?\<beta>] by (cases \<alpha>; auto)

      next
        case W\<^sub>\<beta>_notempty

        (** We attract to the region W\<^sub>\<beta> for \<beta>. *)
        define B where "B = attractor ?\<beta> W\<^sub>\<beta>"
        with W\<^sub>\<beta>_notempty W_comp have "B\<noteq>{}" "B \<subseteq> V"
          using attractor_subset attractor_subset_graph by blast+

        (** Since removing an attractor from the game gives a valid subgame, the game V-B is a
            valid subgame. *)
        interpret subgame': paritygame "Restr E (V-B)" "V-B" "V\<^sub>0-B"
          using attractor_subgame [OF B_def] by blast

        (** By our IH, we once again have two winning region in V-B, X\<^sub>\<alpha> and X\<^sub>\<beta>. *)
        from \<open>B\<noteq>{}\<close> \<open>B\<subseteq>V\<close> have "V-B \<subset> V" by blast
        from psubset.IH[OF this subgame'.paritygame_axioms]
        obtain X\<^sub>\<alpha> X\<^sub>\<beta> where
          X_comp: "V-B = X\<^sub>\<alpha> \<union> X\<^sub>\<beta>" and
          X_disj: "X\<^sub>\<alpha> \<inter> X\<^sub>\<beta> = {}" and
          X\<^sub>\<alpha>_win: "subgame'.winning_region \<alpha> X\<^sub>\<alpha>" and
          X\<^sub>\<beta>_win: "subgame'.winning_region ?\<beta> X\<^sub>\<beta>"
          using opponent.simps(2) apply (cases \<alpha>)
          by fastforce (metis Int_commute Un_commute)

        (** Now, the whole graph consists of X\<^sub>\<alpha> and X\<^sub>\<beta> \<union> B. *)
        from X_comp \<open>B\<subseteq>V\<close> have V_comp: "V = X\<^sub>\<alpha> \<union> (X\<^sub>\<beta>\<union>B)" by blast

        (** These two regions are disjoint. *)
        moreover from X_comp X_disj have disj: "X\<^sub>\<alpha> \<inter> (X\<^sub>\<beta>\<union>B) = {}" by auto

        (** If a subgame is obtained by an attractor for a player, then a winning region for the
            opponent of that player in the subgame is still a winning region in the whole game. *)
        moreover from X\<^sub>\<alpha>_win B_def have "winning_region \<alpha> X\<^sub>\<alpha>"
          using attractor_subgame_winning_region[OF subgame'.paritygame_axioms]
          using subgame'.winning_region_in_V by force

        (** The combined region X\<^sub>\<beta> \<union> B is a winning region for \<beta>. *)
        moreover have "winning_region ?\<beta> (X\<^sub>\<beta>\<union>B)"
        proof -
          (** We get the winning strategy for X\<^sub>\<beta>. *)
          from X\<^sub>\<beta>_win obtain \<sigma> where
            \<sigma>_strat: "subgame'.strategy_of_player ?\<beta> \<sigma>" and
            \<sigma>_dom: "dom \<sigma> = subgame'.V_player ?\<beta> \<inter> X\<^sub>\<beta>" and
            \<sigma>_ran: "ran \<sigma> \<subseteq> X\<^sub>\<beta>" and
            \<sigma>_win: "\<forall>x\<in>X\<^sub>\<beta>. \<forall>ys.
              reachable_cycle (subgame'.induced_subgraph \<sigma>) x ys \<longrightarrow> player_wins_list ?\<beta> ys" and
            \<sigma>_closed: "Restr E (V-B) `` (X\<^sub>\<beta> \<inter> subgame'.V_opponent ?\<beta>) \<subseteq> X\<^sub>\<beta>"
            unfolding subgame'.winning_region_strat by auto

          (** If an edge from a node in X\<^sub>\<beta> exists in G[\<sigma>], then the destination of that edge is
              never a node in X\<^sub>\<alpha>. *)
          {
            fix x y assume "x \<in> X\<^sub>\<beta>" and edge: "(x,y)\<in>induced_subgraph \<sigma>"
            (** x either lies in the domain of \<sigma>, or it does not. *)
            consider (in_dom) "x \<in> dom \<sigma>" | (notin_dom) "x \<notin> dom \<sigma>" by blast
            hence "y\<notin>X\<^sub>\<alpha>" proof cases
              (** If it does, y lies in the range of \<sigma>, which is X\<^sub>\<beta>.
                  Because X\<^sub>\<alpha> and X\<^sub>\<beta> are disjoint, y is not a node in X\<^sub>\<alpha>. *)
              case in_dom with \<sigma>_ran X_disj show ?thesis
                using ind_subgraph_edge_dst[OF edge] by auto

            next
              (** If x does not lie in the domain of \<sigma>, we do a proof by contradiction,
                  and assume that y lies in X\<^sub>\<alpha>. *)
              case notin_dom
              show ?thesis proof
                assume "y\<in>X\<^sub>\<alpha>"
                (** This means the edge exists in V-B. *)
                with \<open>x\<in>X\<^sub>\<beta>\<close> edge \<sigma>_dom X_comp have "(x,y) \<in> Restr E (V-B)"
                  by (cases \<alpha>; simp add: V\<^sub>1_def subgame'.V\<^sub>1_def)
                (** In V-B, all successors of \<alpha>-nodes in X\<^sub>\<beta> lie in X\<^sub>\<beta>.
                    Because X\<^sub>\<alpha> and X\<^sub>\<beta> are disjoint, we have a contradiction. *)
                with \<open>x\<in>X\<^sub>\<beta>\<close> \<open>y\<in>X\<^sub>\<alpha>\<close> notin_dom \<sigma>_dom \<sigma>_closed X_disj
                show False
                  by (cases \<alpha>; simp add: V\<^sub>1_def subgame'.V\<^sub>1_def) blast+
              qed
            qed
          } note X\<^sub>\<beta>_succ=this

          (** In subgames obtained by removing an attractor for a player, the winning region for
              that player's opponent will also be a winning region in the whole game.
              W\<^sub>\<beta> is winning for \<beta> in the subgame V-A, so it is a winning region in the whole game.
              Furthermore, we can extend a winning region with an attractor, which means that
              B is now a winning region for \<beta>. *)
          from A_def B_def W\<^sub>\<beta>_win have "winning_region ?\<beta> B"
            using attractor_subgame_winning_region[OF subgame.paritygame_axioms]
            using attractor_extends_winning_region
            using subgame.winning_region_in_V by auto
          (** We now obtain the winning strategy for B. *)
          then obtain \<sigma>' where
            \<sigma>'_strat: "strategy_of_player ?\<beta> \<sigma>'" and
            \<sigma>'_dom: "dom \<sigma>' = ?V\<^sub>\<beta> \<inter> B" and
            \<sigma>'_ran: "ran \<sigma>' \<subseteq> B" and
            \<sigma>'_win: "\<forall>x\<in>B. \<forall>ys.
              reachable_cycle (induced_subgraph \<sigma>') x ys \<longrightarrow> player_wins_list ?\<beta> ys" and
            \<sigma>'_closed: "E `` (B \<inter> ?V\<^sub>\<alpha>) \<subseteq> B"
            unfolding winning_region_strat
            using V_opponent_opponent V_player_opponent by auto

          (** The winning strategy for X\<^sub>\<beta> \<union> B is the combination of \<sigma> and \<sigma>'. *)
          let ?\<tau> = "\<sigma> ++ \<sigma>'"
          let ?G\<tau> = "induced_subgraph ?\<tau>"
          (** The domains of \<sigma> and \<sigma>' are disjoint, which is useful for future properties. *)
          from \<sigma>_dom \<sigma>'_dom have \<tau>_doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}"
            by (cases \<alpha>; auto simp: V\<^sub>1_def subgame'.V\<^sub>1_def)
          note \<tau>_subgames = ind_subgraph_add_disjoint[OF this]

          (** \<sigma> and \<sigma>' are both valid strategies for \<beta>, so their combination is also valid. *)
          from \<sigma>_strat \<sigma>'_strat have \<tau>_strat: "strategy_of_player ?\<beta> ?\<tau>"
            unfolding subgame'.strategy_of_player_def strategy_of_player_def
            using subgame_strategy_of_V_player[OF subgame'.paritygame_axioms]
            by simp

          (** The two domains combined cover all \<beta>-nodes in X\<^sub>\<beta> \<union> B. *)
          moreover from \<sigma>_dom \<sigma>'_dom have \<tau>_dom: "dom ?\<tau> = ?V\<^sub>\<beta> \<inter> (X\<^sub>\<beta>\<union>B)"
            by (cases \<alpha>; simp add: V\<^sub>1_def subgame'.V\<^sub>1_def) force+

          (** The range of \<sigma> lies in X\<^sub>\<beta>, and the range of \<sigma>' lies in B, so the combined strategy
              has its range in the union of the two regions. *)
          moreover from \<sigma>_ran \<sigma>'_ran have \<tau>_ran: "ran ?\<tau> \<subseteq> (X\<^sub>\<beta>\<union>B)"
            using ran_map_add[OF \<tau>_doms_disj] by blast

          (** The region B is closed in G[\<tau>] because it was closed in G[\<sigma>'], and the games are the
              same in the region B. *)
          moreover from \<tau>_dom \<sigma>'_dom \<sigma>'_ran \<sigma>'_closed \<open>B\<subseteq>V\<close>
          have \<tau>_closed_B: "?G\<tau> `` B \<subseteq> B"
            using \<tau>_subgames(2) apply clarsimp
            subgoal for y x apply (cases "x \<in> dom ?\<tau>")
              subgoal using ind_subgraph_edge_dst[of x y \<sigma>'] by blast
              subgoal apply (cases \<alpha>; clarsimp simp: V\<^sub>1_def)
                using ind_subgraph_edge_in_E[of x y ?\<tau>] by blast+
              done
            done

          (** G[\<tau>] is closed in X\<^sub>\<beta> \<union> B because it is closed in B, and any edge from X\<^sub>\<beta> can only go
              to X\<^sub>\<beta> or to B. *)
          moreover from \<tau>_ran \<tau>_closed_B X\<^sub>\<beta>_succ V_comp
          have \<tau>_closed: "?G\<tau> `` (X\<^sub>\<beta>\<union>B) \<subseteq> (X\<^sub>\<beta>\<union>B)"
            using \<tau>_subgames(1) apply clarsimp
            subgoal for y x apply (cases "x \<in> dom ?\<tau>")
              subgoal using ind_subgraph_edge_dst[of x y ?\<tau>] by auto
              subgoal using ind_subgraph_edge_in_E E_closed_V by blast
              done
            done

          (** Every reachable cycle from B \<union> X\<^sub>\<beta> in G[\<tau>] is won by \<beta>. *)
          moreover
          {
            fix x ys
            assume "x\<in>X\<^sub>\<beta>\<union>B"
               and reachable_cycle: "reachable_cycle ?G\<tau> x ys"
            (** We get the origin y of our reachable cycle. *)
            then obtain y where
              cycle: "cycle ?G\<tau> y ys" and
              y_in_ys: "y \<in> set ys"
              unfolding reachable_cycle_def
              using origin_in_cycle by fast

            (** This cycle is contained entirely within X\<^sub>\<beta> \<union> B because of the closedess of this
                region in G[\<tau>]. *)
            from \<open>x\<in>X\<^sub>\<beta>\<union>B\<close> reachable_cycle \<tau>_closed
            have ys_in_B_X\<^sub>\<beta>: "set ys \<subseteq> X\<^sub>\<beta> \<union> B"
              using reachable_cycle_closed_set by meson

            (** Now we look at a case where the cycle intersects with B, and a case where the
                cycle is entirely contained in X\<^sub>\<beta>. *)
            then consider (B_in_ys) "set ys \<inter> B \<noteq> {}" | (ys_in_X\<^sub>\<beta>) "set ys \<subseteq> X\<^sub>\<beta>" by blast
            hence "player_wins_list ?\<beta> ys" proof cases
              (** If ys intersects with B, the whole cycle has to be contained in B because B is
                  closed in G[\<tau>]. This means the cycle exists in G[\<sigma>'], and is also reachable in
                  that subgame. Any such cycle in G[\<sigma>'] is won by \<beta>, so this one is too. *)
              case B_in_ys
              have ys_in_B: "set ys \<subseteq> B" proof -
                (** We get the version of our cycle that starts in B. *)
                from B_in_ys obtain y' ys' where
                  sets_eq: "set ys' = set ys" and
                  y'_in_B: "y' \<in> B" and
                  cycle_y': "cycle ?G\<tau> y' ys'"
                  using cycle_intermediate_node[OF cycle] by blast
                (** Because B is closed in G[\<tau>], the whole cycle is contained in B. *)
                thus ?thesis
                  using cycle_closed_set[OF _ \<tau>_closed_B] by blast
              qed
              with y_in_ys have "y \<in> B" by blast

              (** Because the whole cycle is contained in B, it exists in G[\<sigma>'].
                  Furthermore, it is also reachable in that subgame. *)
              moreover from subgraph_cycle[OF \<tau>_subgames(2) cycle]
              have "reachable_cycle (induced_subgraph \<sigma>') y ys"
                by (simp add: cycle_impl_reachable_cycle)

              (** All reachable cycles from B in G[\<sigma>'] are won by \<beta>, so this one is too. *)
              ultimately show ?thesis using \<sigma>'_win by blast
            next
              (** If the cycle is contained within X\<^sub>\<beta>, it also exists in G[\<sigma>] in V-B.
                  Every reachable cycle in G[\<sigma>] in V-B is won by \<beta>, so this one is too.*)
              case ys_in_X\<^sub>\<beta>
              with y_in_ys have "y \<in> X\<^sub>\<beta>" by blast

              (** The cycle is a reachable cycle in G[\<sigma>] in V-B. *)
              moreover have "reachable_cycle (subgame'.induced_subgraph \<sigma>) y ys"
              proof -
                (** G[\<tau>] is a subgraph of G[\<sigma>] in V-B in the region X\<^sub>\<beta>. *)
                from X_comp \<tau>_doms_disj have
                  "Restr ?G\<tau> X\<^sub>\<beta> \<subseteq> subgame'.induced_subgraph \<sigma>"
                  unfolding induced_subgraph_def subgame'.induced_subgraph_def
                  unfolding E_of_strat_def by auto
                (** The cycle is contained in X\<^sub>\<beta>, so it also exists in G[\<sigma>] in V-B. *)
                from subgraph_cycle[OF this cycle_restr_V[OF cycle ys_in_X\<^sub>\<beta>]]
                show ?thesis by (simp add: cycle_impl_reachable_cycle)
              qed

              (** All reachable cycles from X\<^sub>\<beta> in G[\<sigma>] in V-B are won by \<beta>.
                  This cycle is reachable from X\<^sub>\<beta> and exists in G[\<sigma>] in V-B, so it is also
                  won by \<beta>. *)
              ultimately show ?thesis using \<sigma>_win by blast
            qed
          } note \<tau>_winning=this

          (** By the former properties, X\<^sub>\<beta> \<union> B is a winning region for \<beta> with the combined
              strategy \<tau>. *)
          ultimately show ?thesis
            unfolding winning_region_strat
            using V_comp V_player_opponent closed_ind_subgraph_opp
            by (intro conjI exI[where x="?\<tau>"]; simp) blast
        qed

        (** We now have two disjoint maximal winning regions, X\<^sub>\<alpha> and X\<^sub>\<beta>\<union>B. *)
        ultimately show ?thesis
          by (cases \<alpha>; simp) blast+
      qed
    qed
  qed
qed (** End of proof maximal_winning_regions *)

(** We use the former lemmas in this file to finally show positional determinancy. *)
section \<open>Positional Determinancy\<close>
context paritygame begin
(** All nodes are won by one of the two players. *)
lemma all_v_won:
  assumes "v\<in>V"
  shows "won_by EVEN v \<or> won_by ODD v"
  using assms maximal_winning_regions[OF paritygame_axioms] winning_region_won_by
  by blast

(** Nodes are not won by both players. *)
lemma v_won_by_one_player: "\<not>(won_by EVEN v \<and> won_by ODD v)"
  using won_by_player_not_won_by_opponent by fastforce

(** Nodes are always won exclusively by one of the two players. *)
theorem v_positionally_determined:
  assumes "v\<in>V"
  shows "won_by EVEN v \<noteq> won_by ODD v"
  using all_v_won[OF \<open>v\<in>V\<close>] v_won_by_one_player by blast
end (** End of context paritygame. *)

end
