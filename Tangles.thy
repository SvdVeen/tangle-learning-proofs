theory Tangles
imports Main ParityGames WinningRegions StrongConnectivity
begin
chapter \<open>Tangles\<close>
(** Van Dijk defines a p-tangle as follows:
      A p-tangle is a nonempty set of vertices U \<subseteq> V with p = pr(U),
      for which player \<alpha> \<equiv>\<^sub>2 p has a strategy \<sigma>: U\<^sub>\<alpha> \<rightarrow> U, such that the graph (U,E'),
      with E' := E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)), is strongly connected and player \<alpha> wins all cycles in (U,E').
    We will work with a variant that does not have a specified p. *)
section \<open>Tangles for Arbitrary Players\<close>
context player_paritygame begin
subsection \<open>Tangle Subgraphs\<close>
(** In Van Dijk's definition, we have E' := E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)).
    This is our dedicated definition for this subgraph. *)
definition player_tangle_subgraph :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v dgraph" where
  "player_tangle_subgraph U \<sigma> \<equiv> E \<inter> (E_of_strat \<sigma> \<union> ((U \<inter> V\<^sub>\<beta>) \<times> U))"

(** A tangle subgraph is a subgraph of the whole graph. *)
lemma player_tangle_subgraph_subgraph:
  "player_tangle_subgraph U \<sigma> \<subseteq> E"
  unfolding player_tangle_subgraph_def by blast

(** The nodes in a tangle subgraph exist in the whole graph. *)
lemma player_tangle_subgraph_nodes_in_V:
  "EV (player_tangle_subgraph U \<sigma>) \<subseteq> V"
  unfolding player_tangle_subgraph_def
  using E_in_V by auto

(** Van Dijk's definition of a tangle's subgraph E' is the same as the induced subgraph of
    the tangle strategy over its domain, restricted to U. This equality makes it easier to use
    tangle definitions with lemmas for general parity games. *)
lemma player_tangle_subgraph_is_restricted_ind_subgraph:
  assumes "U \<subseteq> V"
  assumes "dom \<sigma> = U \<inter> V\<^sub>\<alpha>"
  assumes "ran \<sigma> \<subseteq> U"
  shows "player_tangle_subgraph U \<sigma> = induced_subgraph \<sigma> \<inter> (U\<times>U)"
  unfolding player_tangle_subgraph_def induced_subgraph_def E_of_strat_def
  using assms by (auto simp: ranI)


subsection \<open>Tangle Strategies\<close>
(** The tangle strategy as defined by Van Dijk:
    Player \<alpha>'s strategy \<sigma>:U\<^sub>\<alpha>\<rightarrow>U such that its tangle subgraph E' is strongly connected and \<alpha> wins
    all cycles in (U,E') *)
definition player_tangle_strat :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "player_tangle_strat U \<sigma> \<equiv> strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V\<^sub>\<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
   (let E' = player_tangle_subgraph U \<sigma> in (
      strongly_connected E' U \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle E' v xs \<longrightarrow> winning_player xs)
   ))"


subsection \<open>Tangles\<close>
(** We say that a tangle for a player is a nonempty set of vertices U in V, where the player wins
    pr(U), and there exists a strategy \<sigma> that is a tangle strategy for the player. *)
definition player_tangle :: "'v set \<Rightarrow> bool" where
  "player_tangle U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> winningP (pr_set U) \<and> (\<exists>\<sigma>. player_tangle_strat U \<sigma>)"

lemma player_tangle_nonempty[simp]: "\<not>player_tangle {}"
  unfolding player_tangle_def by simp

lemma player_tangle_in_V: "player_tangle U \<Longrightarrow> U \<subseteq> V"
  unfolding player_tangle_def by simp

lemma fin_player_tangle: "player_tangle U \<Longrightarrow> finite U"
  using finite_subset[OF player_tangle_in_V fin_V] .

lemma player_wins_player_tangle: "player_tangle U \<Longrightarrow> winningP (pr_set U)"
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

  (** The tangle strategy will function as the winning region strategy. *)
  from player_tangle obtain \<sigma> where
      \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>"
  and \<sigma>_dom: "dom \<sigma> = U \<inter> V\<^sub>\<alpha>"
  and \<sigma>_ran: "ran \<sigma> \<subseteq> U"
  and \<sigma>_winning: "\<forall>v\<in>U. \<forall>xs. cycle (player_tangle_subgraph U \<sigma>) v xs \<longrightarrow> winning_player xs"
    unfolding player_tangle_def player_tangle_strat_def Let_def by auto

  (** We show that all cycles in U are won in the induced subgraph of \<sigma>. *)
  have \<sigma>_winning_subgraph: "\<forall>u\<in>U. \<forall>ys. reachable_cycle (induced_subgraph \<sigma>) u ys
      \<longrightarrow> winning_player ys"
  proof (rule ballI; rule allI; rule impI)
    fix u ys
    assume u_in_U: "u \<in> U" and cycle_u_ys: "reachable_cycle (induced_subgraph \<sigma>) u ys"

    (** We know that U is closed for the opponent, and that \<sigma> only goes to U.
        Therefore, the induced subgraph of \<sigma> is closed in U, which means that the cycle
        stays in U. *)
    from \<sigma>_dom U_closed_opp have "induced_subgraph \<sigma> `` U \<subseteq> U"
      using ind_subgraph_closed_region[OF U_in_V _ \<sigma>_ran] by blast
    from reachable_cycle_closed_set[OF u_in_U this cycle_u_ys]
    have ys_in_U: "set ys \<subseteq> U" .

    (** We take only the cycle at the end of the reachable_cycle. We know that it starts in U. *)
    from cycle_u_ys ys_in_U obtain y where
        cycle_y_ys: "cycle (induced_subgraph \<sigma>) y ys" and
        y_in_U: "y \<in> U"
      unfolding reachable_cycle_def
      using origin_in_cycle by fastforce

    (** The subgraph of \<sigma> restructed to U is part of its tangle subgraph, so the cycle is won
        by the known properties of \<sigma>. *)
    have "induced_subgraph \<sigma> \<inter> (U\<times>U) \<subseteq> player_tangle_subgraph U \<sigma>"
      using player_tangle_subgraph_is_restricted_ind_subgraph[OF U_in_V \<sigma>_dom \<sigma>_ran] by simp
    from \<sigma>_winning y_in_U subgraph_cycle[OF this cycle_restr_V[OF cycle_y_ys ys_in_U]]
      show "winning_player ys" by simp
  qed

  (** We now prove that \<sigma> is a winning region strategy. *)
  show ?thesis
    unfolding player_winning_region_def
    apply (simp add: U_in_V)
    apply (rule exI[where x="\<sigma>"]; intro conjI)
      subgoal using \<sigma>_strat .
      subgoal using \<sigma>_dom Int_commute ..
      subgoal using \<sigma>_ran .
      subgoal using U_closed_opp .
      subgoal using \<sigma>_winning_subgraph .
    done
qed

lemma subgame_player_tangle_is_player_tangle:
  assumes "player_paritygame E' V' V\<^sub>0' V\<^sub>\<alpha>'"
  assumes "E' = Restr E V'"
  assumes "V' \<subseteq> V"
  assumes "V\<^sub>\<alpha>' = V\<^sub>\<alpha> \<inter> V'"
  shows "player_paritygame.player_tangle E' V' pr V\<^sub>\<alpha>' winningP U \<Longrightarrow> player_tangle U"
proof -
  assume subgame_tangle: "player_paritygame.player_tangle E' V' pr V\<^sub>\<alpha>' winningP U"
  show ?thesis
    unfolding player_tangle_def
  proof (intro conjI)
    from assms(2) have E'_subseteq_E: "E' \<subseteq> E" by simp

    from subgame_tangle show U_notempty: "U \<noteq> {}"
      unfolding player_paritygame.player_tangle_def[OF assms(1)] by blast

    from subgame_tangle have U_in_V': "U \<subseteq> V'"
      unfolding player_paritygame.player_tangle_def[OF assms(1)] by blast
    with assms(3) show U_in_V: "U \<subseteq> V" by blast

    from subgame_tangle show U_winning_pr: "winningP (pr_set U)"
      unfolding player_paritygame.player_tangle_def[OF assms(1)] by blast

    from subgame_tangle obtain \<sigma> where
      \<sigma>_strat_subgame: "arena.strategy_of E' V\<^sub>\<alpha>' \<sigma>" and
      \<sigma>_dom_subgame: "dom \<sigma> = U \<inter> V\<^sub>\<alpha>'" and
      \<sigma>_ran: "ran \<sigma> \<subseteq> U " and
      \<sigma>_tangle_subgraph_connected_subgame:
        "strongly_connected (player_paritygame.player_tangle_subgraph E' V' V\<^sub>\<alpha>' U \<sigma>)
            U" and
      \<sigma>_won_subgame:
        "\<forall>v\<in>U. \<forall>xs. cycle (player_paritygame.player_tangle_subgraph E' V' V\<^sub>\<alpha>' U \<sigma>) v xs
            \<longrightarrow> winning_player xs"
      unfolding player_paritygame.player_tangle_def[OF assms(1)]
                player_paritygame.player_tangle_strat_def[OF assms(1)]
                Let_def by blast
    have subgame_is_arena: "arena E' V' V\<^sub>0'"
      using paritygame.axioms[OF player_paritygame.axioms(1)[OF assms(1)]] .

    from \<sigma>_strat_subgame have \<sigma>_strat: "strategy_of V\<^sub>\<alpha> \<sigma>"
      unfolding strategy_of_def arena.strategy_of_def[OF subgame_is_arena]
      using assms(2,4) by blast

    from \<sigma>_dom_subgame assms(4) U_in_V' have \<sigma>_dom: "dom \<sigma> = U \<inter> V\<^sub>\<alpha>" by auto

    from assms(2,3) E'_subseteq_E U_in_V' have subgame_tangle_subgraph_is_tangle_subgraph:
      "player_paritygame.player_tangle_subgraph E' V' V\<^sub>\<alpha>' U \<sigma> = player_tangle_subgraph U \<sigma>"
      unfolding player_paritygame.player_tangle_subgraph_def[OF assms(1)] player_tangle_subgraph_def
      unfolding assms(4)
      apply (safe)
      subgoal by blast
      subgoal using \<sigma>_strat_subgame arena.strategy_of_in_E[OF subgame_is_arena] by blast
      subgoal using \<sigma>_strat_subgame arena.strategy_of_in_E[OF subgame_is_arena] by blast
      subgoal by fast
      subgoal by blast
      subgoal by blast
      done

    from \<sigma>_tangle_subgraph_connected_subgame have \<sigma>_tangle_subgraph_connected:
      "strongly_connected (player_tangle_subgraph U \<sigma>) U"
      unfolding subgame_tangle_subgraph_is_tangle_subgraph by blast

    from \<sigma>_won_subgame have \<sigma>_won:
      "\<forall>v\<in>U. \<forall>xs. cycle (player_tangle_subgraph U \<sigma>) v xs \<longrightarrow> winning_player xs"
      unfolding subgame_tangle_subgraph_is_tangle_subgraph by blast


    show "\<exists>\<sigma>. player_tangle_strat U \<sigma>"
      unfolding player_tangle_strat_def Let_def
      apply (rule exI[where x=\<sigma>]; intro conjI)
      subgoal using \<sigma>_strat .
      subgoal using \<sigma>_dom .
      subgoal using \<sigma>_ran .
      subgoal using \<sigma>_tangle_subgraph_connected .
      subgoal using \<sigma>_won .
      done
  qed
qed

subsection \<open>Escapes\<close>
(** The escapes are the set of nodes outside of a tangle that the opponent can move to *)
definition opponent_escapes :: "'v set \<Rightarrow> 'v set" where
  "opponent_escapes t \<equiv> {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V\<^sub>\<beta> \<and> v \<in> V-t}"

lemma opponent_escapes_in_V: "opponent_escapes t \<subseteq> V"
  unfolding opponent_escapes_def by auto

lemma fin_opponent_escapes[simp]: "finite (opponent_escapes t)"
  using finite_subset[OF opponent_escapes_in_V fin_V] .

lemma player_tangle_escapes: "player_tangle U
  \<Longrightarrow> (\<forall>v\<in>U \<inter> V\<^sub>\<beta>. \<forall>w. (v,w) \<in> E \<longrightarrow> w \<in> U \<or> w \<in> opponent_escapes U)"
  unfolding opponent_escapes_def
  using E_in_V by auto

lemma no_escapes_closed_opponent: "opponent_escapes t = {} \<longleftrightarrow> E `` (t \<inter> V\<^sub>\<beta>) \<subseteq> t"
  unfolding opponent_escapes_def
  using E_closed_V by blast
end (** End of context player_paritygame. *)


section \<open>Tangles for Specific Players\<close>
(** We pull all prior definitions into the context of specified players. *)
context paritygame begin
subsection \<open>Tangle Subgraphs\<close>
fun tangle_subgraph :: "player \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> 'v dgraph" where
  "tangle_subgraph EVEN = P0.player_tangle_subgraph"
| "tangle_subgraph ODD = P1.player_tangle_subgraph"

(** This lemma shows that the definition matches Van Dijk's, and is easier to work with in this
    context. *)
lemma tangle_subgraph_eq:
  "tangle_subgraph \<alpha> U \<sigma> = E \<inter> (E_of_strat \<sigma> \<union> ((U \<inter> V_opponent \<alpha>)) \<times> U)"
  using P0.player_tangle_subgraph_def P1.player_tangle_subgraph_def
  by (cases \<alpha>; simp add: V\<^sub>1_def V_diff_diff_V\<^sub>0)

lemma tangle_subgraph_is_restricted_ind_subgraph:
  assumes "U \<subseteq> V"
  assumes "dom \<sigma> = U \<inter> V_player \<alpha>"
  assumes "ran \<sigma> \<subseteq> U"
  shows "tangle_subgraph \<alpha> U \<sigma> = induced_subgraph \<sigma> \<inter> (U\<times>U)"
  using P0.player_tangle_subgraph_is_restricted_ind_subgraph[OF assms(1) _ assms(3)]
  using P1.player_tangle_subgraph_is_restricted_ind_subgraph[OF assms(1) _ assms(3)]
  using assms(2) by (cases \<alpha>; simp add: V\<^sub>1_def)


subsection \<open>Tangle Strategies\<close>
fun tangle_strat :: "player \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "tangle_strat EVEN = P0.player_tangle_strat"
| "tangle_strat ODD = P1.player_tangle_strat"

(** This lemma shows that the definition matches Van Dijk's, and lets us get easier to work with
    properties. *)
lemma tangle_strat_iff:
  "tangle_strat \<alpha> U \<sigma> \<longleftrightarrow> strategy_of (V_player \<alpha>) \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
   (let E' = tangle_subgraph \<alpha> U \<sigma> in (
      strongly_connected E' U \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
   ))"
  using P0.player_tangle_strat_def P1.player_tangle_strat_def
  by (cases \<alpha>; simp)


subsection \<open>Tangles\<close>
fun tangle :: "player \<Rightarrow> 'v set \<Rightarrow> bool" where
  "tangle EVEN = P0.player_tangle"
| "tangle ODD = P1.player_tangle"

(** This lemma shows that the definition matches Van Dijk's, and lets us get easier to work with
    properties. *)
lemma tangle_iff:
  "tangle \<alpha> U \<longleftrightarrow> U \<noteq> {} \<and> U \<subseteq> V \<and> player_winningP \<alpha> (pr_set U) \<and> (\<exists>\<sigma>. tangle_strat \<alpha> U \<sigma>)"
  using P0.player_tangle_def P1.player_tangle_def
  by (cases \<alpha>; simp)

lemma tangle_notempty[simp]: "\<not>tangle \<alpha> {}"
  using tangle_iff by simp

lemma tangle_in_V: "tangle \<alpha> U \<Longrightarrow> U \<subseteq> V"
  using tangle_iff by simp

lemma fin_tangle: "tangle \<alpha> U \<Longrightarrow> finite U"
  using finite_subset[OF tangle_in_V fin_V] .

lemma player_wins_tangle: "tangle \<alpha> U \<Longrightarrow> player_winningP \<alpha> (pr_set U)"
  using tangle_iff by simp

lemma closed_tangle_is_winning_region:
  assumes "tangle \<alpha> U"
  assumes "E `` (U \<inter> V_opponent \<alpha>) \<subseteq> U"
  shows "winning_region \<alpha> U"
  using P0.closed_player_tangle_is_winning_region P1.closed_player_tangle_is_winning_region
  using assms by (cases \<alpha>; simp add: V\<^sub>1_def V_diff_diff_V\<^sub>0)

(** TODO: cleanup of this proof *)
lemma subgame_tangle_is_tangle:
  assumes "paritygame E' V' V\<^sub>0'"
  assumes "E' = Restr E V'"
  assumes "V' \<subseteq> V"
  assumes "V\<^sub>0' = V\<^sub>0 \<inter> V'"
  shows "paritygame.tangle E' V' V\<^sub>0' pr \<alpha> U \<Longrightarrow> tangle \<alpha> U"
proof -
  assume subgame_tangle: "paritygame.tangle E' V' V\<^sub>0' pr \<alpha> U"

  have subgame_is_arena: "arena E' V' V\<^sub>0'"
    using paritygame.axioms[OF assms(1)] .
  have subgame_is_finite_graph_V_Succ:  "finite_graph_V_Succ E' V'"
    using arena.axioms[OF subgame_is_arena] by blast
  have subgame_is_finite_graph_V: "finite_graph_V E' V'"
    using finite_graph_V_Succ.axioms[OF subgame_is_finite_graph_V_Succ] by blast

  from subgame_tangle show "tangle \<alpha> U"
  proof (cases \<alpha>; simp add: paritygame.tangle.simps[OF assms(1)])
    case EVEN
    with subgame_tangle paritygame.tangle.simps[OF assms(1)]
    have player_tangle: "player_paritygame.player_tangle E' V' pr V\<^sub>0' even U" by simp

    have subgame_is_player_paritygame: "player_paritygame E' V' V\<^sub>0' V\<^sub>0'"
      apply (unfold_locales)
      subgoal using subgame_is_finite_graph_V by (simp add: finite_graph_V.E_in_V)
      subgoal using subgame_is_finite_graph_V by (simp add: finite_graph_V.fin_V)
      subgoal using subgame_is_finite_graph_V_Succ by (simp add: finite_graph_V_Succ.succ)
      subgoal using subgame_is_arena by (simp add: arena.V\<^sub>0_in_V)
      subgoal by simp
      done
    from P0.subgame_player_tangle_is_player_tangle[OF subgame_is_player_paritygame assms(2,3,4) player_tangle]
    show "P0.player_tangle U" .
  next
    case ODD
    with subgame_tangle paritygame.tangle.simps[OF assms(1)]
    have player_tangle: "player_paritygame.player_tangle E' V' pr (arena.V\<^sub>1 V' V\<^sub>0') odd U" by simp

    have subgame_is_player_paritygame: "player_paritygame E' V' V\<^sub>0' (arena.V\<^sub>1 V' V\<^sub>0')"
      apply (unfold_locales)
      subgoal using subgame_is_finite_graph_V by (simp add: finite_graph_V.E_in_V)
      subgoal using subgame_is_finite_graph_V by (simp add: finite_graph_V.fin_V)
      subgoal using subgame_is_finite_graph_V_Succ by (simp add: finite_graph_V_Succ.succ)
      subgoal using subgame_is_arena by (simp add: arena.V\<^sub>0_in_V)
      subgoal unfolding arena.V\<^sub>1_def[OF subgame_is_arena] by simp
      subgoal by simp
      done
    from assms(3,4) have "arena.V\<^sub>1 V' V\<^sub>0' = V\<^sub>1 \<inter> V'"
      unfolding arena.V\<^sub>1_def[OF subgame_is_arena] V\<^sub>1_def
      by fastforce

    from P1.subgame_player_tangle_is_player_tangle[OF subgame_is_player_paritygame assms(2,3) this player_tangle]
    show "P1.player_tangle U" .
  qed
qed


subsection \<open>Escapes\<close>
fun escapes :: "player \<Rightarrow> 'v set \<Rightarrow> 'v set" where
  "escapes EVEN = P0.opponent_escapes"
| "escapes ODD = P1.opponent_escapes"

(** This lemma shows that the definition matches Van Dijk's, and is easier to work with in this
    context. *)
lemma escapes_eq: "escapes \<alpha> t = {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V_opponent \<alpha> \<and> v \<in> V-t}"
  using P0.opponent_escapes_def P1.opponent_escapes_def
  by (cases \<alpha>; simp add: V\<^sub>1_def V_diff_diff_V\<^sub>0)

lemma escapes_in_V: "escapes \<alpha> t \<subseteq> V"
  using P0.opponent_escapes_in_V P1.opponent_escapes_in_V
  by (cases \<alpha>; simp)

lemma fin_escapes[simp]: "finite (escapes \<alpha> t)"
  using finite_subset[OF escapes_in_V fin_V] .

lemma tangle_escapes: "tangle \<alpha> U
  \<Longrightarrow> (\<forall>v\<in>U \<inter> V_opponent \<alpha>. \<forall>w. (v,w) \<in> E \<longrightarrow> w \<in> U \<or> w \<in> escapes \<alpha> U)"
  using P0.player_tangle_escapes P1.player_tangle_escapes
  by (cases \<alpha>; simp add: V\<^sub>1_def V_diff_diff_V\<^sub>0)

lemma no_escapes_closed: "escapes \<alpha> t = {} \<longleftrightarrow> E `` (t \<inter> V_opponent \<alpha>) \<subseteq> t"
  using P0.no_escapes_closed_opponent P1.no_escapes_closed_opponent
  by (cases \<alpha>; simp add: V\<^sub>1_def V_diff_diff_V\<^sub>0)
end (** End of context paritygame. *)

end
