theory PositionalDeterminancy
imports Main Attractors WinningRegions
begin

(** We use a proof for positional determinancy to check our definitions. *)
chapter \<open>Positional Determinancy\<close>
section \<open>Auxiliary Lemmas\<close>

context paritygame begin
(** We can extend a winning region with a maximal attractor. *)
lemma attractor_extends_winning_region:
  assumes "winning_region \<alpha> W"
  shows "winning_region \<alpha> (attractor \<alpha> W)"
proof -
  let ?V\<^sub>\<alpha> = "V_player \<alpha>"
  define X where "X = attractor \<alpha> W"
  have W_in_X: "W \<subseteq> X" unfolding X_def using attractor_subset by simp
  have X_in_V: "X \<subseteq> V" unfolding X_def
    using attractor_subset_graph[OF winning_region_in_V[OF assms]] by simp

  obtain \<sigma> where
      \<sigma>_strat: "strategy_of_player \<alpha> \<sigma>"
  and \<sigma>_dom: "dom \<sigma> = (X-W) \<inter> ?V\<^sub>\<alpha>"
  and \<sigma>_ran: "ran \<sigma> \<subseteq> X"
  and \<sigma>_closed: "\<forall>v\<in>X-W. \<forall>v'. (v,v') \<in> induced_subgraph \<sigma> \<longrightarrow> v'\<in>X"
  and \<sigma>_forces_W: "\<forall>v\<in>X. \<forall>vs. lasso' (induced_subgraph \<sigma>) v vs \<longrightarrow> set vs \<inter> W \<noteq> {}"
    unfolding X_def strategy_of_player_def using attractor_attracts[of \<alpha> W] by blast

  from assms obtain \<sigma>' where
      \<sigma>'_strat: "strategy_of_player \<alpha> \<sigma>'"
  and \<sigma>'_dom: "dom \<sigma>' = ?V\<^sub>\<alpha> \<inter> W"
  and \<sigma>'_ran: "ran \<sigma>' \<subseteq> W"
  and \<sigma>'_winning: "\<forall>w\<in>W. \<forall>ys. reachable_cycle (induced_subgraph \<sigma>') w ys \<longrightarrow> player_wins_list \<alpha> ys"
  and \<sigma>'_closed_opp: "E `` (W\<inter>V_opponent \<alpha>) \<subseteq> W"
    using winning_region_strat by force

  from \<sigma>'_closed_opp \<sigma>'_dom have \<sigma>'_closed: "induced_subgraph \<sigma>' `` W \<subseteq> W"
    apply (cases \<alpha>; simp add: V\<^sub>1_def)
    using ind_subgraph_closed_region[OF winning_region_in_V[OF assms] _ \<sigma>'_ran] by blast+

  (** We combine the two strategies, which forms a winning strategy for the new region. *)
  let ?\<tau> = "\<sigma> ++ \<sigma>'"
  let ?\<tau>_subgame = "induced_subgraph ?\<tau>"
  from \<sigma>_dom \<sigma>'_dom have \<tau>_doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}" by auto

  (** \<tau> is a strategy of the player. *)
  from \<sigma>_strat \<sigma>'_strat have \<tau>_strat: "strategy_of_player \<alpha> ?\<tau>"
    unfolding strategy_of_player_def by simp

  (** The domain of \<tau> is all of the player's vertices in X. *)
  from \<sigma>_dom \<sigma>'_dom W_in_X have \<tau>_dom: "dom ?\<tau> = ?V\<^sub>\<alpha> \<inter> X" by auto

  (** The range of \<tau> is in X. *)
  from \<sigma>_ran \<sigma>'_ran W_in_X have \<tau>_ran: "ran ?\<tau> \<subseteq> X"
    using ran_map_add[OF \<tau>_doms_disj] by simp

  (** The subgame of \<tau> is closed in W. *)
  from \<sigma>'_closed have \<tau>_closed_W: "?\<tau>_subgame `` W \<subseteq> W"
    unfolding induced_subgraph_def E_of_strat_def by auto

  (** The subgame of \<tau> is closed in X. *)
  have \<tau>_closed_X: "?\<tau>_subgame `` X \<subseteq> X"
    apply clarsimp
    subgoal for y x apply (cases "x \<in> W")
      subgoal using W_in_X \<tau>_closed_W  by auto
      subgoal using \<sigma>_closed ind_subgraph_add_disjoint(1)[OF \<tau>_doms_disj] by blast
      done
    done

  (** X is closed for the opponent, regardless of \<tau>. *)
  from \<tau>_closed_X \<tau>_dom have X_closed_opp: "E `` (X\<inter>V_opponent \<alpha>) \<subseteq> X"
    using ind_subgraph_notin_dom
    by (cases \<alpha>; simp add: V\<^sub>1_def) blast+

  (** All cycles reachable from X are won by the player under \<tau>. *)
  have \<tau>_winning: "\<forall>v\<in>X. \<forall>ys. reachable_cycle ?\<tau>_subgame v ys \<longrightarrow> player_wins_list \<alpha> ys"
  proof (rule ballI; rule allI; rule impI)
    fix v ys
    assume v_in_X: "v\<in>X" and reachable_cycle: "reachable_cycle ?\<tau>_subgame v ys"
    hence ys_notempty: "ys\<noteq>[]" by auto

    from reachable_cycle_closed_set[OF v_in_X \<tau>_closed_X reachable_cycle]
    have ys_in_X: "set ys \<subseteq> X" .

    from reachable_cycle obtain y where
      cycle: "cycle ?\<tau>_subgame y ys"
      unfolding reachable_cycle_def by blast
    with ys_in_X have y_in_X: "y \<in> X"
      using origin_in_cycle by fast

    have W_in_ys: "set ys \<inter> W \<noteq> {}"
    proof (rule ccontr; simp)
      assume no_W_in_ys: "set ys \<inter> W = {}"
      with ys_in_X have ys_in_X_min_W: "set ys \<subseteq> X-W" by blast

      from \<sigma>_dom \<sigma>'_dom have "Restr ?\<tau>_subgame (X-W) \<subseteq> induced_subgraph \<sigma>"
        unfolding induced_subgraph_def E_of_strat_def by auto
      from subgraph_cycle[OF this cycle_restr_V[OF cycle ys_in_X_min_W]]
      have "lasso' (induced_subgraph \<sigma>) y ys"
        using cycle_impl_lasso' by fast

      with \<sigma>_forces_W y_in_X no_W_in_ys show "False" by blast
    qed

    from cycle_intersects_closed_region[OF cycle W_in_ys \<tau>_closed_W]
    have ys_in_W: "set ys \<subseteq> W" .
    hence y_in_W: "y\<in>W"
      using origin_in_cycle[OF cycle] by blast

    have "Restr ?\<tau>_subgame W \<subseteq> induced_subgraph \<sigma>'"
      unfolding induced_subgraph_def E_of_strat_def by auto
    from subgraph_cycle[OF this cycle_restr_V[OF cycle ys_in_W]]
    have "reachable_cycle (induced_subgraph \<sigma>') y ys"
      using cycle_impl_reachable_cycle ys_notempty by fast

    with \<sigma>'_winning y_in_W
    show "player_wins_list \<alpha> ys" by blast
  qed

  (** Using the prior properties, we can show that B is won by the opponent. *)
  show "winning_region \<alpha> X"
    using winning_region_strat
    using X_in_V \<tau>_strat \<tau>_dom \<tau>_ran \<tau>_winning X_closed_opp by blast
qed

(** If we remove a maximal attractor from a game, the remainder is a valid parity game. *)
lemma attractor_subgame:
  assumes X: "X = attractor \<alpha> T"
  assumes E': "E' = E \<inter> (V-X)\<times>(V-X)"
  assumes V': "V' = V-X"
  assumes V\<^sub>0': "V\<^sub>0' = V\<^sub>0-X"
  shows "paritygame E' V' V\<^sub>0'"
proof (unfold_locales)
  from E' V' show "E' \<subseteq> V' \<times> V'" by simp
  from V' show "finite V'" by simp
  from V\<^sub>0' V' show "V\<^sub>0'\<subseteq>V'" using V\<^sub>0_in_V by blast
  show "\<And>v. v \<in> V' \<Longrightarrow> E' `` {v} \<noteq> {}"
  proof -
    fix v assume v_in_V': "v\<in>V'"
    hence v_in_V: "v\<in>V" using V' by simp
    from v_in_V' V' have "v \<notin> X" by simp
    with notin_attractor_succ[OF v_in_V] X
    have "E `` {v} - X \<noteq> {}" by simp
    then obtain w where w: "(v,w) \<in> E \<and> w \<in> V - X" using E_in_V by blast
    with E' V' v_in_V' have "(v,w)\<in>E'" using E_in_V by blast
    then show "E' `` {v} \<noteq> {}" by blast
  qed
qed

(** If we remove some set from a game and the result is a valid subgame, then its player nodes
    are a subset of the player nodes in the whole game. *)
lemma subgame_V_player_subset:
  assumes "paritygame E' V' V\<^sub>0'"
  assumes V': "V' = V-S"
  assumes V\<^sub>0': "V\<^sub>0' = V\<^sub>0-S"
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
  assumes "paritygame E' V' V\<^sub>0'"
  assumes E'_subset_E: "E' \<subseteq> E"
  assumes V'_def: "V' = V-S"
  assumes V\<^sub>0'_def: "V\<^sub>0' = V\<^sub>0-S"
  shows "arena.strategy_of E' (paritygame.V_player V' V\<^sub>0' \<alpha>) \<sigma>
    \<Longrightarrow> strategy_of (V_player \<alpha>) \<sigma>"
proof -
  interpret subgame: paritygame E' V' V\<^sub>0' by fact
  from subgame_V_player_subset[OF subgame.paritygame_axioms V'_def V\<^sub>0'_def]
  have V_player_subset: "subgame.V_player \<alpha> \<subseteq> V_player \<alpha>" by blast
  assume "subgame.strategy_of (subgame.V_player \<alpha>) \<sigma>"
  thus ?thesis
    unfolding subgame.strategy_of_def strategy_of_def E_of_strat_def
    using E'_subset_E V_player_subset by blast
qed

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

  let ?\<sigma>_subgraph = "induced_subgraph \<sigma>"

  from \<sigma>_strat_subgame E'_def have \<sigma>_strat: "strategy_of_player \<alpha> \<sigma>"
    unfolding strategy_of_player_def subgame.strategy_of_player_def
    using subgame_strategy_of_V_player[OF subgame.paritygame_axioms _ V'_def V\<^sub>0'_def] by simp

  from \<sigma>_dom_subgame have \<sigma>_dom: "dom \<sigma> = V_player \<alpha> \<inter> W"
    using V\<^sub>1_def subgame.V\<^sub>1_def V'_def V\<^sub>0'_def subgame.V_player.simps W_in_V'
    by (cases \<alpha>) auto

  have \<sigma>_closed: "?\<sigma>_subgraph `` W \<subseteq> W"
  proof clarsimp
    fix w w'
    assume w_in_W: "w\<in>W" and edge_in_subgraph: "(w,w')\<in>?\<sigma>_subgraph"
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

  have \<sigma>_winning: "\<forall>w\<in>W. \<forall>ys. reachable_cycle ?\<sigma>_subgraph w ys \<longrightarrow> player_wins_list \<alpha> ys"
  proof (rule ballI; rule allI; rule impI)
    fix w ys
    assume w_in_W: "w\<in>W" and cycle_w_ys: "reachable_cycle ?\<sigma>_subgraph w ys"
    hence ys_notempty: "ys\<noteq>[]" by auto

    from \<sigma>_closed have "?\<sigma>_subgraph `` W \<subseteq> W" by blast
    from reachable_cycle_closed_set[OF w_in_W this cycle_w_ys]
    have ys_in_W: "set ys \<subseteq> W" .

    from cycle_w_ys ys_in_W obtain w' where
      path_w'_ys_w': "path ?\<sigma>_subgraph w' ys w'" and
      w'_in_W: "w'\<in>W"
      using reachable_cycle_paths[of ?\<sigma>_subgraph] origin_in_path by fastforce

    have "Restr ?\<sigma>_subgraph W \<subseteq> subgame.induced_subgraph \<sigma>"
      using ind_subgraph_restr_subarena[OF subgame.arena_axioms, of \<sigma>]
      using W_in_V' unfolding V'_def E'_def by auto
    from subgraph_path[OF this path_restr_V[OF path_w'_ys_w' ys_in_W w'_in_W]] ys_notempty
    have "reachable_cycle (subgame.induced_subgraph \<sigma>) w' ys"
      using loop_impl_reachable_cycle by fast

    with \<sigma>_winning_subgame w'_in_W
    show "player_wins_list \<alpha> ys" by blast
  qed

  from W_in_V W_closed_opp \<sigma>_strat \<sigma>_dom \<sigma>_ran \<sigma>_winning show ?thesis
    by (auto simp: winning_region_strat)
qed
end (** End of context paritygame. *)


section \<open>Maximal Winning Regions\<close>
(** Every game can be split into two disjoint winning regions. *)
lemma maximal_winning_regions:
  fixes V :: "'v set"
  assumes "paritygame E V V\<^sub>0"
  shows "\<exists>W\<^sub>0 W\<^sub>1. V = W\<^sub>0 \<union> W\<^sub>1 \<and> W\<^sub>0 \<inter> W\<^sub>1 = {}
    \<and> paritygame.winning_region E V V\<^sub>0 pr EVEN W\<^sub>0
    \<and> paritygame.winning_region E V V\<^sub>0 pr ODD W\<^sub>1"
proof -
  have "finite V" proof -
    interpret paritygame E V V\<^sub>0 by fact
    show ?thesis by blast
  qed
  thus ?thesis using assms
  proof (induction arbitrary: E V\<^sub>0 rule: finite_psubset_induct)
    case (psubset V)
    then consider (V_empty) "V = {}" | (V_notempty) "V \<noteq> {}" by fast
    thus ?case proof cases
      case V_empty thus ?thesis
        using paritygame.winning_region_empty psubset.prems by fastforce
    next
      case V_notempty

      interpret paritygame E V V\<^sub>0 by fact

      have fin_pr: "finite (pr`V)" by simp

      (** Get the highest priority p in V. *)
      define p :: "nat" where "p = pr_set V"

      (** Get the player who wins p. *)
      then obtain \<alpha> :: player where "\<alpha> = player_wins_pr p" by simp
      hence player_wins_p: "player_winningP \<alpha> p"
        by (cases \<alpha>; simp add: player_wins_pr_def split: if_splits)
      (** Useful shorthand for later. *)
      let ?V\<^sub>\<alpha> = "V_player \<alpha>"
      let ?\<beta> = "opponent \<alpha>"
      let ?V\<^sub>\<beta> = "V_player ?\<beta>"

      (** Get any v of the highest priority. *)
      obtain v :: "'v" where v_in_V: "v \<in> V" and v_pr: "pr v = p"
        using pr_set_exists[OF fin_V V_notempty] unfolding p_def by blast

      (** Any list that contains v will have p as its top priority, and thus it is won by \<alpha> if it is a play. *)
      have player_wins_v: "\<forall>vs. set vs \<subseteq> V \<and> v \<in> set vs \<longrightarrow> player_wins_list \<alpha> vs"
        using p_def player_wins_p pr_V_in_list v_pr by fastforce

      (** Attract to that v. *)
      define A :: "'v set" where "A = attractor \<alpha> {v}"

      (** Take the subgraph with A removed. *)
      define V' :: "'v set" where "V' = V - A"
      define E' :: "'v rel" where "E' = E \<inter> ((V-A) \<times> (V-A))"
      define V\<^sub>0' :: "'v set" where "V\<^sub>0' = V\<^sub>0 - A"

      (** Show that V is the union of V' and A. *)
      from \<open>v\<in>V\<close> have A_in_V: "A \<subseteq> V" unfolding A_def using attractor_subset_graph by simp
      from Diff_partition[OF this] have V_composed_of: "V = V' \<union> A" unfolding V'_def by blast

      (** Show that every edge in E that does not touch A is also in E'. *)
      have edge_E_to_E': "\<forall>v v'. (v,v')\<in>E \<and> v \<notin> A \<and> v' \<notin> A \<longleftrightarrow> (v,v') \<in> E'"
        unfolding E'_def using E_in_V by auto

      (** Show that the subgame is a valid arena. *)
      from attractor_subgame[OF A_def E'_def V'_def V\<^sub>0'_def]
      interpret subgame: paritygame E' V' V\<^sub>0' pr .

      have "E' \<subseteq> E" unfolding E'_def using E_in_V by simp
      note subgame_propagate_strategy_of_V_player =
        subgame_strategy_of_V_player[OF subgame.paritygame_axioms this V'_def V\<^sub>0'_def]

      (** Show that V' is a strict subset of V; this is needed for applying the induction hypothesis. *)
      have V'_subset: "V' \<subset> V"
        unfolding V'_def A_def
        using v_in_V attractor_subset by blast

      (** Take the winning regions W\<^sub>0 and W\<^sub>1 in the subgame. *)
      from psubset.IH[OF V'_subset subgame.paritygame_axioms]
      obtain W\<^sub>0 W\<^sub>1 where
        V'_comp: "V' = W\<^sub>0 \<union> W\<^sub>1" and
        W_disjoint: "W\<^sub>0 \<inter> W\<^sub>1 = {}" and
        W\<^sub>0_winning_EVEN_subgame: "subgame.winning_region EVEN W\<^sub>0" and
        W\<^sub>1_winning_ODD_subgame: "subgame.winning_region ODD W\<^sub>1"
        by blast

      (** Take the winning region for the opponent of \<alpha>. *)
      define W :: "'v set" where
      "W \<equiv> if \<alpha> = EVEN then W\<^sub>1 else W\<^sub>0"
      from W\<^sub>0_winning_EVEN_subgame W\<^sub>1_winning_ODD_subgame
      have W_winning_opponent_subgame: "subgame.winning_region ?\<beta> W"
        unfolding W_def by (cases \<alpha>; simp)
      have W_in_V': "W \<subseteq> V'"
        unfolding W_def using V'_comp by simp
      hence W_in_V: "W \<subseteq> V" using V'_subset by auto

      (** Attract for the opponent to their winning region in V'. *)
      define B :: "'v set" where "B = attractor ?\<beta> W"
      have B_in_V: "B \<subseteq> V" unfolding B_def using attractor_subset_graph[OF W_in_V] by simp

      (** B is now a winning region for the opponent. *)
      from A_def W_winning_opponent_subgame have "winning_region ?\<beta> W"
        using attractor_subgame_winning_region[OF subgame.paritygame_axioms E'_def V'_def V\<^sub>0'_def W_in_V']
        by simp
      hence B_winning_opponent: "winning_region ?\<beta> B"
        unfolding B_def using attractor_extends_winning_region by simp

      (** We must consider the possibility that B is empty, because the original W might have been
          empty. *)
      consider (B_nonempty) "B \<noteq> {}" | (B_empty) "B = {}" by blast
      thus ?thesis proof cases
        case B_nonempty
        (** take the subgame of G-B. *)
        define V'' :: "'v set" where "V'' = V - B"
        define E'' :: "'v rel" where "E'' = E \<inter> (V-B)\<times>(V-B)"
        define V\<^sub>0'' :: "'v set" where "V\<^sub>0'' = V\<^sub>0 - B"

        have V''_in_V: "V''\<subseteq>V" unfolding V''_def by blast
        have V''_B_disj: "V'' \<inter> B = {}" unfolding V''_def by blast

        have edge_E_to_E'': "\<forall>v v'. (v,v')\<in>E \<and> v \<notin> B \<and> v' \<notin> B \<longleftrightarrow> (v,v') \<in> E''"
        unfolding E''_def using E_in_V by auto

        from attractor_subgame[OF B_def E''_def V''_def V\<^sub>0''_def]
        interpret subgame': paritygame E'' V'' V\<^sub>0'' .

        have "E'' \<subseteq> E" unfolding E''_def using E_in_V by simp
        note subgame'_propagate_strategy_of_V_player =
          subgame_strategy_of_V_player[OF subgame'.paritygame_axioms this V''_def V\<^sub>0''_def]

        have V''_subset: "V'' \<subset> V"
          unfolding V''_def
          using B_nonempty B_in_V by blast

        from psubset.IH[OF V''_subset subgame'.paritygame_axioms]
        obtain X\<^sub>0 X\<^sub>1 where
          V''_comp: "V'' = X\<^sub>0 \<union> X\<^sub>1" and
          X_disj: "X\<^sub>0 \<inter> X\<^sub>1 = {}" and
          X\<^sub>0_winning_EVEN_subgame': "subgame'.winning_region EVEN X\<^sub>0" and
          X\<^sub>1_winning_ODD_subgame': "subgame'.winning_region ODD X\<^sub>1"
          by blast

        (** We want to know which region is won by \<alpha>. *)
        define X\<^sub>\<alpha> where "X\<^sub>\<alpha> \<equiv> if \<alpha> = EVEN then X\<^sub>0 else X\<^sub>1"
        from V''_comp have X\<^sub>\<alpha>_in_V'': "X\<^sub>\<alpha>\<subseteq>V''" unfolding X\<^sub>\<alpha>_def by (cases \<alpha>) auto
        from X\<^sub>0_winning_EVEN_subgame' X\<^sub>1_winning_ODD_subgame'
        have X\<^sub>\<alpha>_winning_\<alpha>_subgame': "subgame'.winning_region \<alpha> X\<^sub>\<alpha>"
          unfolding X\<^sub>\<alpha>_def by (cases \<alpha>; simp)

        (** We want to know which region is won by the opponent. *)
        define X\<^sub>\<beta> where "X\<^sub>\<beta> \<equiv> if \<alpha> = EVEN then X\<^sub>1 else X\<^sub>0"
        from V''_comp have X\<^sub>\<beta>_in_V'': "X\<^sub>\<beta>\<subseteq>V''" unfolding X\<^sub>\<beta>_def by (cases \<alpha>) auto
        with V''_in_V have X\<^sub>\<beta>_in_V: "X\<^sub>\<beta>\<subseteq>V" by simp
        from X\<^sub>0_winning_EVEN_subgame' X\<^sub>1_winning_ODD_subgame'
        have X\<^sub>\<beta>_winning_\<beta>_subgame': "subgame'.winning_region ?\<beta> X\<^sub>\<beta>"
          unfolding X\<^sub>\<beta>_def by (cases \<alpha>; simp)

        (** Now, the other properties of the winning regions from the induction hypothesis also
            hold for the specified regions for \<alpha> and their opponent. *)
        from V''_comp have V''_comp': "V'' = X\<^sub>\<alpha> \<union> X\<^sub>\<beta>"
          unfolding X\<^sub>\<alpha>_def X\<^sub>\<beta>_def by (cases \<alpha>) auto
        from X_disj have X_disj': "X\<^sub>\<alpha> \<inter> X\<^sub>\<beta> = {}"
          unfolding X\<^sub>\<alpha>_def X\<^sub>\<beta>_def by (cases \<alpha>) auto

        from B_in_V V''_comp' have V_comp_X_B: "V = X\<^sub>\<alpha> \<union> (B\<union>X\<^sub>\<beta>)"
          unfolding V''_def by blast

        moreover from X_disj' V''_B_disj V''_comp' have X_B_disj: "X\<^sub>\<alpha> \<inter> (B\<union>X\<^sub>\<beta>) = {}" by blast

        moreover have X\<^sub>\<alpha>_winning_\<alpha>: "winning_region \<alpha> (X\<^sub>\<alpha>)"
          using attractor_subgame_winning_region[OF subgame'.paritygame_axioms E''_def V''_def V\<^sub>0''_def X\<^sub>\<alpha>_in_V'' B_def X\<^sub>\<alpha>_winning_\<alpha>_subgame'] .

        moreover have X\<^sub>\<beta>_B_winning_\<beta>: "winning_region ?\<beta> (B\<union>X\<^sub>\<beta>)"
        proof -
          from B_winning_opponent obtain \<sigma> where
            \<sigma>_strat: "strategy_of_player ?\<beta> \<sigma>" and
            \<sigma>_dom: "dom \<sigma> = ?V\<^sub>\<beta> \<inter> B" and
            \<sigma>_ran: "ran \<sigma> \<subseteq> B" and
            \<sigma>_winning_opp: "\<forall>w\<in>B. \<forall>xs. reachable_cycle (induced_subgraph \<sigma>) w xs
              \<longrightarrow> player_wins_list ?\<beta> xs" and
            \<sigma>_closed_player: "E `` (B\<inter>V_opponent ?\<beta>) \<subseteq> B"
            unfolding winning_region_strat by fastforce

          from \<sigma>_closed_player \<sigma>_dom have \<sigma>_closed: "induced_subgraph \<sigma> `` B \<subseteq> B"
            apply (cases \<alpha>; simp add: V\<^sub>1_def)
            using ind_subgraph_closed_region[OF B_in_V _ \<sigma>_ran] by blast+

          from X\<^sub>\<beta>_winning_\<beta>_subgame' obtain \<sigma>' where
            \<sigma>'_strat_subgame': "subgame'.strategy_of_player ?\<beta> \<sigma>'" and
            \<sigma>'_dom_subgame': "dom \<sigma>' = subgame'.V_player ?\<beta> \<inter> X\<^sub>\<beta>" and
            \<sigma>'_ran: "ran \<sigma>' \<subseteq> X\<^sub>\<beta>" and
            \<sigma>'_winning_opp_subgame': "\<forall>w\<in>X\<^sub>\<beta>. \<forall>xs.
              reachable_cycle (subgame'.induced_subgraph \<sigma>') w xs \<longrightarrow> player_wins_list ?\<beta> xs" and
            \<sigma>'_closed_player_subgame': "E'' `` (X\<^sub>\<beta>\<inter>subgame'.V_opponent ?\<beta>) \<subseteq> X\<^sub>\<beta>"
            unfolding subgame'.winning_region_strat by fastforce

          from \<sigma>'_ran \<sigma>'_closed_player_subgame' \<sigma>'_dom_subgame' X\<^sub>\<beta>_in_V''
          have \<sigma>'_closed_subgame': "subgame'.induced_subgraph \<sigma>' `` X\<^sub>\<beta> \<subseteq> X\<^sub>\<beta>"
            apply clarsimp
            subgoal for y x apply (cases "x \<in> dom \<sigma>'")
              subgoal using subgame'.ind_subgraph_edge_dst by blast
              subgoal using subgame'.v_notin_V_player_in_V_opponent subgame'.ind_subgraph_edge_in_E
                by blast
              done
            done

          from \<sigma>'_strat_subgame' have \<sigma>'_strat: "strategy_of_player ?\<beta> \<sigma>'"
            unfolding strategy_of_player_def subgame'.strategy_of_player_def
            using subgame'_propagate_strategy_of_V_player by simp

          from \<sigma>'_dom_subgame' have \<sigma>'_dom: "dom \<sigma>' = ?V\<^sub>\<beta> \<inter> X\<^sub>\<beta>"
            using V''_comp subgame'.V_player.simps V''_def V\<^sub>0''_def V\<^sub>1_def subgame'.V\<^sub>1_def X\<^sub>\<beta>_def
            by (cases \<alpha>) auto

          (** If we combine the two strategies, we get a winning strategy for B\<union>X\<^sub>\<beta>. *)
          let ?\<tau> = "\<sigma> ++ \<sigma>'"
          let ?\<tau>_subgame = "induced_subgraph ?\<tau>"
          from \<sigma>_dom \<sigma>'_dom V''_B_disj X\<^sub>\<beta>_in_V'' have \<tau>_doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}" by auto

          (** \<tau> is a strategy of the opponent. *)
          from \<sigma>_strat \<sigma>'_strat have \<tau>_strat: "strategy_of_player ?\<beta> ?\<tau>"
            unfolding strategy_of_player_def by simp

          (** The domain of \<tau> is all of the opponent's nodes in B\<union>X\<^sub>\<beta>. *)
          from \<sigma>_dom \<sigma>'_dom have \<tau>_dom: "dom ?\<tau> = ?V\<^sub>\<beta> \<inter> (B\<union>X\<^sub>\<beta>)" by auto

          (** The range of \<tau> is in B\<union>X\<^sub>\<beta>. *)
          from \<sigma>_ran \<sigma>'_ran have \<tau>_ran: "ran ?\<tau> \<subseteq> B\<union>X\<^sub>\<beta>"
            using ran_map_add[OF \<tau>_doms_disj] by blast

          (** \<tau> is closed in B. *)
          from \<sigma>_closed have \<tau>_closed_B: "?\<tau>_subgame `` B \<subseteq> B"
            using ind_subgraph_add_disjoint(1)[OF \<tau>_doms_disj] by blast
          (** \<tau> is closed in B\<union>X\<^sub>\<beta>. *)
          have \<tau>_closed: "?\<tau>_subgame `` (B\<union>X\<^sub>\<beta>) \<subseteq> B\<union>X\<^sub>\<beta>"
            apply clarsimp
            subgoal for y x apply (cases "x \<in> dom ?\<tau>")
              subgoal using \<tau>_ran ind_subgraph_edge_dst[of x y ?\<tau>] by auto
              subgoal apply (cases "x \<in> B"; clarsimp)
                subgoal using \<tau>_closed_B by blast
                subgoal using \<sigma>'_closed_subgame' ind_subgraph_edge_in_E
                  using subgame'.ind_subgraph_notin_dom edge_E_to_E''
                  by blast
                done
              done
            done

          (** All cycles reachable from B\<union>X\<^sub>\<beta> are won by the opponent. *)
          have \<tau>_winning: "\<forall>x\<in>B\<union>X\<^sub>\<beta>. \<forall>ys. reachable_cycle ?\<tau>_subgame x ys \<longrightarrow> player_wins_list ?\<beta> ys"
          proof (rule ballI; rule allI; rule impI)
            fix x ys
            assume x_in_B_X\<^sub>\<beta>: "x\<in>B\<union>X\<^sub>\<beta>" and cycle_x_ys: "reachable_cycle ?\<tau>_subgame x ys"
            from x_in_B_X\<^sub>\<beta> B_in_V X\<^sub>\<beta>_in_V have x_in_V: "x\<in>V" by blast
            from cycle_x_ys have ys_notempty: "ys\<noteq>[]" by auto

            from reachable_cycle_closed_set[OF x_in_B_X\<^sub>\<beta> \<tau>_closed cycle_x_ys]
            have ys_in_B_X\<^sub>\<beta>: "set ys \<subseteq> B \<union> X\<^sub>\<beta>" .

            from cycle_x_ys ys_in_B_X\<^sub>\<beta> obtain y where
              path_y_ys_y: "path ?\<tau>_subgame y ys y" and
              y_in_ys: "y \<in> set ys" and
              y_in_B_X\<^sub>\<beta>: "y \<in> B \<union> X\<^sub>\<beta>"
              using reachable_cycle_paths [of ?\<tau>_subgame x ys] origin_in_path by fast

            from ys_in_B_X\<^sub>\<beta> consider (B_in_ys) "set ys \<inter> B \<noteq> {}" | (ys_in_X\<^sub>\<beta>) "set ys \<subseteq> X\<^sub>\<beta>" by blast
            thus "player_wins_list ?\<beta> ys" proof cases
              case B_in_ys
              have ys_in_B: "set ys \<subseteq> B" proof -
              from B_in_ys obtain y' ys' where
                sets_eq: "set ys' = set ys" and
                y'_in_ys: "y' \<in> set ys" and
                y'_in_B: "y'\<in>B" and
                path_y'_ys'_y': "path ?\<tau>_subgame y' ys' y'"
                using loop_intermediate_node[OF path_y_ys_y] by blast

                from path_closed_set[OF y'_in_B \<tau>_closed_B path_y'_ys'_y'] sets_eq
                show ?thesis by simp
              qed
              with y_in_ys have y_in_B: "y\<in>B" by blast

              have "?\<tau>_subgame \<subseteq> induced_subgraph \<sigma>"
                using ind_subgraph_add_disjoint(1)[OF \<tau>_doms_disj] by blast
              from subgraph_path[OF this path_y_ys_y] ys_notempty
              have "reachable_cycle (induced_subgraph \<sigma>) y ys"
                using loop_impl_reachable_cycle by fast

              with \<sigma>_winning_opp y_in_B show ?thesis by blast
            next
              case ys_in_X\<^sub>\<beta>
              with y_in_ys have y_in_X\<^sub>\<beta>: "y\<in>X\<^sub>\<beta>" by blast

              from V''_comp' \<tau>_doms_disj have "?\<tau>_subgame \<inter> X\<^sub>\<beta>\<times>X\<^sub>\<beta> \<subseteq> subgame'.induced_subgraph \<sigma>'"
                unfolding induced_subgraph_def subgame'.induced_subgraph_def E_of_strat_def
                unfolding E''_def V''_def by auto
              from subgraph_path[OF this path_restr_V[OF path_y_ys_y ys_in_X\<^sub>\<beta> y_in_X\<^sub>\<beta>]] ys_notempty
              have "reachable_cycle (subgame'.induced_subgraph \<sigma>') y ys"
                using loop_impl_reachable_cycle by fast

              with \<sigma>'_winning_opp_subgame' y_in_X\<^sub>\<beta> show ?thesis by blast
            qed
          qed

          (** \<tau> is closed for the player. *)
          from \<tau>_closed have \<tau>_closed_player: "E `` ((B\<union>X\<^sub>\<beta>)\<inter>V_opponent ?\<beta>) \<subseteq> (B\<union>X\<^sub>\<beta>)"
            apply (clarsimp simp: V_opponent_opposite_V_player)
            using \<tau>_dom ind_subgraph_notin_dom by blast

          (** Due to the aforementioned properties, \<tau> is a winning strategy for B\<union>X\<^sub>\<beta>, making it a
              winning region. *)
          from B_in_V X\<^sub>\<beta>_in_V \<tau>_closed_player
          show ?thesis
            apply (simp add: winning_region_strat)
            apply (rule exI[where x="?\<tau>"]; intro conjI)
              subgoal using \<tau>_strat by blast
              subgoal using \<tau>_dom by blast
              subgoal using \<tau>_ran by blast
              subgoal using \<tau>_winning by blast
            done
        qed

        ultimately show ?thesis
          unfolding X\<^sub>\<alpha>_def X\<^sub>\<beta>_def by (cases \<alpha>) auto
      next
        (** Because B is empty, all that remains is the player \<alpha>'s winning region and A
            We should be able to show that this forms one winning region.
            This is because any new cycles introduced in the combination of the player's winning
            region and A must go through A, and thus have a maximum priority that is winning for
            the player \<alpha>. *)
        case B_empty
        (** W is empty because B is empty. *)
        hence W_empty: "W = {}"
          unfolding B_def using attractor_subset by blast
        (** Because W is empty, V' consists only of the winning region of the player. *)
        hence V'_winning_\<alpha>: "subgame.winning_region \<alpha> V'"
          using W_def V'_comp W\<^sub>0_winning_EVEN_subgame W\<^sub>1_winning_ODD_subgame
          by (cases \<alpha>) auto

        (** The entire graph is the winning region for the player. *)
        have "winning_region \<alpha> V"
        proof -
          (** The attractor strategy for A will force all plays in A to v. *)
          obtain \<sigma> where
            \<sigma>_strat: "strategy_of ?V\<^sub>\<alpha> \<sigma>" and
            \<sigma>_dom: "dom \<sigma> = (A-{v}) \<inter> ?V\<^sub>\<alpha>" and
            \<sigma>_ran: "ran \<sigma> \<subseteq> A" and
            \<sigma>_closed: "\<forall>v\<in>A-{v}. \<forall>v'. (v,v') \<in> induced_subgraph \<sigma> \<longrightarrow> v' \<in> A" and
            \<sigma>_forces_v: "\<forall>a\<in>A. \<forall>xs. lasso' (induced_subgraph \<sigma>) a xs \<longrightarrow> set xs \<inter> {v} \<noteq> {}"
            unfolding A_def using attractor_attracts[of \<alpha> "{v}"] by blast

          (** The winning strategy for V' will ensure wins in all cycles staying in V'. *)
          from V'_winning_\<alpha> obtain \<sigma>' where
            \<sigma>'_strat_subgame: "subgame.strategy_of_player \<alpha> \<sigma>'" and
            \<sigma>'_dom_subgame: "dom \<sigma>' = subgame.V_player \<alpha> \<inter> V'" and
            \<sigma>'_ran: "ran \<sigma>' \<subseteq> V'" and
            \<sigma>'_winning_subgame: "\<forall>v'\<in>V'. \<forall>xs. reachable_cycle (subgame.induced_subgraph \<sigma>') v' xs
              \<longrightarrow> player_wins_list \<alpha> xs" and
            \<sigma>'_closed_opponent_subgame: "\<forall>v'\<in>V'. v' \<in> subgame.V_opponent \<alpha> \<longrightarrow> E' `` {v'} \<subseteq> V'"
            unfolding subgame.winning_region_strat by fast
          from \<sigma>'_strat_subgame have \<sigma>'_strat: "strategy_of_player \<alpha> \<sigma>'"
            unfolding strategy_of_player_def subgame.strategy_of_player_def
            using subgame_propagate_strategy_of_V_player by simp
          from \<sigma>'_dom_subgame have \<sigma>'_dom: "dom \<sigma>' = ?V\<^sub>\<alpha> \<inter> V'"
            using V'_def V\<^sub>0'_def V\<^sub>1_def subgame.V\<^sub>1_def subgame.V_player.simps by (cases \<alpha>) auto

          (** Neither strategy has a choice for v, which is necessary if it belongs to the player
              Therefore, we have to add a choice for v to the strategy, which can be any random
              successor. *)
          define v_target where "v_target \<equiv> SOME v'. v' \<in> E `` {v}"
          from v_in_V have v_succ: "\<exists>v'. v' \<in> E `` {v}" using succ by auto

          (** We need to show that the edge from v to the random successor actually exists. *)
          have v_target_edge: "(v,v_target)\<in>E"
            unfolding v_target_def
            using some_in_eq v_succ by blast
          hence v_target_in_V: "v_target \<in> V" using E_in_V by blast

          define v_choice where "v_choice \<equiv> if v \<in> ?V\<^sub>\<alpha> then [v\<mapsto>v_target] else Map.empty"

          (** The domain of v_choice depends on the owner of v. *)
          have v_choice_dom_player: "v \<in> ?V\<^sub>\<alpha> \<longrightarrow> dom v_choice = ?V\<^sub>\<alpha> \<inter> {v}"
            unfolding v_choice_def by simp
          have v_choice_dom_opp: "v \<notin> ?V\<^sub>\<alpha> \<longrightarrow> dom v_choice = {}"
            unfolding v_choice_def by simp
          note v_choice_dom = v_choice_dom_player v_choice_dom_opp

          (** v_choice is a strategy of the player's nodes. *)
          have v_choice_strat: "strategy_of_player \<alpha> v_choice"
            unfolding strategy_of_player_def strategy_of_def
            apply (rule conjI)
              subgoal using v_choice_dom by (cases "v\<in>?V\<^sub>\<alpha>") auto
              subgoal using strategy_of_map_assign v_target_edge
                unfolding v_choice_def strategy_of_def by auto
            done

          (** The range of v_choice is in V. *)
          from v_target_in_V have v_choice_ran: "ran v_choice \<subseteq> V"
            unfolding v_choice_def by simp

          (** Now we can combine the three to form a winning strategy for V. *)
          let ?\<tau> = "\<sigma> ++ \<sigma>' ++ v_choice"
          let ?\<tau>_subgame = "induced_subgraph ?\<tau>"

          (** The domains of the three strategies are disjoint. *)
          from \<sigma>_dom \<sigma>'_dom have \<sigma>_\<sigma>'_dom_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}"
            unfolding A_def V'_def by force
          from \<sigma>_dom v_choice_dom have \<sigma>_v_choice_dom_disj: "dom \<sigma> \<inter> dom v_choice = {}"
            by blast
          from \<sigma>'_dom v_choice_dom have \<sigma>'_v_choice_dom_disj: "dom \<sigma>' \<inter> dom v_choice = {}"
            apply (cases "v\<in>?V\<^sub>\<alpha>"; simp add: V'_def A_def)
            using attractor_subset by blast

          (** \<tau> is a strategy of the player. *)
          from \<sigma>_strat \<sigma>'_strat v_choice_strat have \<tau>_strat: "strategy_of_player \<alpha> ?\<tau>"
            unfolding strategy_of_player_def by simp

          (** The domain of \<tau> is all of the player's nodes in V. *)
          from \<sigma>_dom \<sigma>'_dom have \<tau>_dom: "dom ?\<tau> = ?V\<^sub>\<alpha> \<inter> V"
            unfolding strategy_of_def
            apply (cases "v\<in>?V\<^sub>\<alpha>"; simp add: v_choice_dom)
            using V_composed_of v_in_V by blast+

          (** The range of \<tau> is in V. *)
          from \<sigma>_ran \<sigma>'_ran v_choice_ran have \<tau>_ran: "ran ?\<tau> \<subseteq> V"
          proof -
            from \<sigma>_ran \<sigma>'_ran have \<sigma>\<sigma>'_ran: "ran (\<sigma> ++ \<sigma>') \<subseteq> V"
              using V_composed_of ran_map_add[OF \<sigma>_\<sigma>'_dom_disj] by blast
            from \<sigma>_v_choice_dom_disj \<sigma>'_v_choice_dom_disj
            have disj: "dom (\<sigma> ++ \<sigma>') \<inter> dom v_choice = {}" by auto
            from \<sigma>\<sigma>'_ran v_choice_ran show ?thesis
              using ran_map_add[OF disj] by simp
          qed

          (** \<tau> is closed in A. *)
          have \<tau>_closed_A: "\<forall>a\<in>A-{v}. \<forall>a'. (a,a') \<in> ?\<tau>_subgame \<longrightarrow> a' \<in> A"
          proof (rule ballI; rule allI; rule impI)
            fix a a'
            assume a_in_A_min_v: "a\<in>A-{v}" and edge_in_\<tau>: "(a,a')\<in>?\<tau>_subgame"
            with \<sigma>_dom \<sigma>'_dom v_choice_dom have edge_in_\<sigma>: "(a,a')\<in>induced_subgraph \<sigma>"
              unfolding induced_subgraph_def E_of_strat_def V'_def
              apply simp by blast
            with a_in_A_min_v \<sigma>_closed show "a'\<in>A" by blast
          qed

          (** \<tau> forces all plays in A to go to v. *)
          have \<tau>_forces_v: "\<forall>a\<in>A. \<forall>vs. lasso' ?\<tau>_subgame a vs \<longrightarrow> set vs \<inter> {v} \<noteq> {}"
          proof (rule ballI; rule allI; rule impI; rule ccontr; simp)
            fix a vs
            assume a_in_A: "a\<in>A" and
                   lasso'_a_vs: "lasso' ?\<tau>_subgame a vs" and
                   v_notin_vs: "v \<notin> set vs"

            from lasso'_a_vs have a_in_vs: "a\<in>set vs" using origin_in_lasso' by fast
            with a_in_A v_notin_vs have a_in_A_min_v: "a\<in>A-{v}" by blast

            from lasso'_a_vs obtain a' where a'_in_vs: "a'\<in>set vs" and
              path_a_vs_a': "path ?\<tau>_subgame a vs a'"
              using lasso'_impl_path by fast

            from v_notin_vs \<tau>_closed_A
            have vs_in_A_min_v: "set vs \<subseteq> A-{v}"
              using path_partially_closed_set[OF a_in_A_min_v _ path_a_vs_a'] by blast

            from \<sigma>'_dom v_choice_dom
            have "Restr ?\<tau>_subgame (A-{v}) \<subseteq> induced_subgraph \<sigma>"
              unfolding induced_subgraph_def E_of_strat_def V'_def by auto
            from subgraph_lasso'[OF this lasso'_restr_V[OF lasso'_a_vs vs_in_A_min_v]]
            have "lasso' (induced_subgraph \<sigma>) a vs" .

            from \<sigma>_forces_v a_in_A this have "set vs \<inter> {v} \<noteq> {}" by blast
            with v_notin_vs show "False" by blast
          qed

          (** \<tau> wins all cycles reachable in the graph. *)
          have \<tau>_winning: "\<forall>x\<in>V. \<forall>ys. reachable_cycle ?\<tau>_subgame x ys \<longrightarrow> player_wins_list \<alpha> ys"
          proof (rule ballI; rule allI; rule impI)
            fix x ys
            assume x_in_V: "x\<in>V" and cycle_x_ys: "reachable_cycle ?\<tau>_subgame x ys"
            from cycle_x_ys have ys_notempty: "ys\<noteq>[]" by auto
            from reachable_cycle_in_V[OF x_in_V ind_subgraph_reachable_cycle[OF cycle_x_ys]]
            have ys_in_V: "set ys \<subseteq> V" .

            from cycle_x_ys obtain y where
              path_y_ys_y: "path ?\<tau>_subgame y ys y" and
              y_in_ys: "y \<in> set ys"
              using reachable_cycle_paths[of ?\<tau>_subgame x ys] origin_in_path by fast

            consider (A_in_ys) "set ys \<inter> A \<noteq> {}" | (A_notin_ys) "set ys \<inter> A = {}" by blast
            thus "player_wins_list \<alpha> ys" proof cases
              case A_in_ys
              then obtain y' where y'_in_ys: "y'\<in>set ys" and y'_in_A: "y'\<in>A" by blast
              from loop_intermediate_node[OF path_y_ys_y y'_in_ys]
              obtain ys' where sets_eq: "set ys' = set ys" and
                path_y'_ys'_y': "path ?\<tau>_subgame y' ys' y'"
                by blast
              from sets_eq ys_notempty have ys'_notempty: "ys'\<noteq>[]" by force

              with y'_in_A loop_impl_lasso'[OF path_y'_ys'_y' ys'_notempty] \<tau>_forces_v sets_eq
              have "v \<in> set ys" by fastforce
              with player_wins_v ys_in_V show ?thesis by simp
            next
              case A_notin_ys

              from ys_in_V A_notin_ys y_in_ys have y_in_V': "y\<in>V'"
                unfolding V'_def by blast
              from ys_in_V A_notin_ys V_composed_of have ys_in_V': "set ys \<subseteq> V'" by blast

              from \<sigma>'_v_choice_dom_disj have "Restr ?\<tau>_subgame V' \<subseteq> subgame.induced_subgraph \<sigma>'"
                unfolding induced_subgraph_def subgame.induced_subgraph_def E_of_strat_def
                unfolding V'_def E'_def by auto
              from subgraph_path[OF this path_restr_V[OF path_y_ys_y ys_in_V' y_in_V']] ys_notempty
              have "reachable_cycle (subgame.induced_subgraph \<sigma>') y ys"
                using loop_impl_reachable_cycle by fastforce

              with \<sigma>'_winning_subgame y_in_V' show ?thesis by blast
            qed
          qed

          (** Trivially, V is closed. *)
          have \<tau>_closed_opponent: "E `` (V\<inter>?V\<^sub>\<beta>) \<subseteq> V" using E_in_V by auto

          (** Using the prior properties, we can show that \<tau> is the winning strategy for the game. *)
          thus "winning_region \<alpha> V"
            apply (simp add: winning_region_strat V_player_opponent)
            apply (rule exI[where x="?\<tau>"]; intro conjI)
              subgoal using \<tau>_strat by blast
              subgoal using \<tau>_dom by blast
              subgoal using \<tau>_ran by blast
              subgoal using \<tau>_winning by blast
            done
        qed

        thus ?thesis
          apply (cases \<alpha>; simp)
            subgoal by fastforce
            subgoal using P0.player_winning_region_empty by blast
          done
      qed
    qed
  qed
qed (**End of proof maximal_winning_regions. *)

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

(** Nodes are always won won exclusively by one of the two players. *)
theorem v_won_by_disjoint:
  assumes "v\<in>V"
  shows "won_by EVEN v \<noteq> won_by ODD v"
  using all_v_won[OF assms] v_won_by_one_player by blast
end (** End of context paritygame. *)

end
