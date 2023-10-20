theory ParityGames
imports Main Strategies
begin
chapter \<open>Parity Games\<close>
(** This section contains all definitions specific to parity games *)
section \<open>Parity Game Definitions\<close>

locale paritygame = arena E V V\<^sub>0
  for E V and V\<^sub>0 :: "'v set" +
  fixes pr :: "'v \<Rightarrow> nat"
begin
  definition top_pr :: "'v list \<Rightarrow> nat" where
    "top_pr xs \<equiv> MAX v \<in> set xs. pr v"

  definition pr_set :: "'v set \<Rightarrow> nat" where
    "pr_set S \<equiv> Max (pr ` S)"
end

locale player_paritygame = paritygame E V V\<^sub>0 pr
  for E V and V\<^sub>0 :: "'v set" and pr +
  fixes V\<^sub>\<alpha> :: "'v set"
  fixes winningP :: "nat \<Rightarrow> bool"
  assumes V\<^sub>\<alpha>_subset: "V\<^sub>\<alpha> \<subseteq> V"
  assumes V\<^sub>\<alpha>_player: "V\<^sub>\<alpha> = V\<^sub>0 \<or> V\<^sub>\<alpha> = V\<^sub>1"
begin
  (** Shorthand for the opponent's vertices *)
  abbreviation (input) V\<^sub>\<beta> :: "'v set" where
    "V\<^sub>\<beta> \<equiv> V-V\<^sub>\<alpha>"

  (** If the player owns a node, it has successors in any strategy of the player's nodes,
      and its successors in any strategy of the opponent's nodes are the same as its successors
      in the entire graph. *)
  lemma player_induced_succs:
    "\<lbrakk>v\<in>V\<^sub>\<alpha>; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    "\<lbrakk>v\<in>V\<^sub>\<alpha>; strategy_of V\<^sub>\<beta> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} = E `` {v}"
    unfolding induced_subgraph_def E_of_strat_def strategy_of_def V\<^sub>1_def
      subgoal using succ[of v] V\<^sub>\<alpha>_subset apply (cases "v\<in>dom \<sigma>") by blast+
      subgoal by auto
    done

  (** If the opponent owns a node, it has successors in any strategy of the opponent's nondes,
      and its successors in any strategy of the player's nodes are the same as its successors
      in the entire graph *)
  lemma opponent_induced_succs:
    "\<lbrakk>v\<in>V\<^sub>\<beta>; strategy_of V\<^sub>\<beta> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    "\<lbrakk>v\<in>V\<^sub>\<beta>; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} = E `` {v}"
    unfolding induced_subgraph_def E_of_strat_def strategy_of_def V\<^sub>1_def
      subgoal using succ[of v] by (cases "v\<in>dom \<sigma>") auto
      subgoal by auto
    done

  (** The intersection of two opposing players' induced subgraphs is a valid parity game *)
  lemma ind_subgraph_inter_opposed:
    assumes G\<sigma>: "G\<sigma> = induced_subgraph (dom \<sigma>) \<sigma>"
    assumes G\<sigma>': "G\<sigma>' = induced_subgraph (dom \<sigma>') \<sigma>'"
    assumes \<sigma>_player: "strategy_of V\<^sub>\<alpha> \<sigma>"
    assumes \<sigma>'_opp: "strategy_of V\<^sub>\<beta> \<sigma>'"
    shows "paritygame (G\<sigma> \<inter> G\<sigma>') V V\<^sub>0"
  proof (unfold_locales)
    show "G\<sigma> \<inter> G\<sigma>' \<subseteq> V\<times>V"
      unfolding G\<sigma> using ind_subgraph E_in_V by blast
    show "finite V" by simp
    show "V\<^sub>0\<subseteq>V" using V\<^sub>0_in_V by simp
    show "\<And>v. v \<in> V \<Longrightarrow> (G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}"
    proof (cases)
      fix v
      assume v_player: "v\<in>V\<^sub>\<alpha>"
      with \<sigma>'_opp have "G\<sigma>' `` {v} = E `` {v}"
        unfolding G\<sigma>' using player_induced_succs by simp
      moreover from v_player \<sigma>_player have "G\<sigma> `` {v} \<noteq> {}"
        unfolding G\<sigma> using player_induced_succs by blast
      moreover have "G\<sigma> \<subseteq> E" unfolding G\<sigma> by simp
      ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by auto
    next
      fix v
      assume "v\<in>V" "v\<notin>V\<^sub>\<alpha>"
      hence v_opp: "v\<in>V-V\<^sub>\<alpha>" by auto
      with \<sigma>_player have "G\<sigma> `` {v} = E `` {v}"
        unfolding G\<sigma> using opponent_induced_succs by simp
      moreover from v_opp \<sigma>'_opp have "G\<sigma>' `` {v} \<noteq> {}"
        unfolding G\<sigma>' using opponent_induced_succs by simp
      moreover have "G\<sigma>' \<subseteq> E" unfolding G\<sigma>' using ind_subgraph by simp
      ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" using succ[of v] by blast
    qed
  qed
end (** locale player_paritygame *)


subsection \<open>Winning Regions\<close>
context player_paritygame begin

  abbreviation "winning_player xs \<equiv> winningP (top_pr xs)"
  abbreviation "winning_opponent xs \<equiv> \<not>winningP (top_pr xs)"

  (** A winning region is a region in the graph where one player has a strategy that makes it
      closed, and where every cycle reachable from every node in that region is won by that
      player *)
  definition player_winning_region :: "'v set \<Rightarrow> bool" where
    "player_winning_region W \<equiv> W\<subseteq>V \<and> (\<exists>\<sigma>.
      strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> W \<and> ran \<sigma> \<subseteq> W \<and>
      (\<forall>v\<in>W. \<forall>xs. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_player xs) \<and>
       E `` (W \<inter> V\<^sub>\<beta>) \<subseteq> W)"

  lemma player_winning_region_empty[simp]: "player_winning_region {}"
    unfolding player_winning_region_def strategy_of_def E_of_strat_def
    by auto

  (** The winning region exists in the graph *)
  lemma player_winning_region_in_V: "player_winning_region W \<Longrightarrow> W\<subseteq>V"
    unfolding player_winning_region_def by simp

  (** This definition exists for symmetry *)
  definition losing_region :: "'v set \<Rightarrow> bool" where
    "losing_region W \<equiv> (W\<subseteq>V \<and> (\<exists>\<sigma>.
      strategy_of V\<^sub>\<beta> \<sigma> \<and> dom \<sigma> = V\<^sub>\<beta> \<inter> W \<and> ran \<sigma> \<subseteq> W \<and>
      (\<forall>v\<in>W. \<forall>xs. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_opponent xs) \<and>
      E `` (W\<inter>V\<^sub>\<alpha>) \<subseteq> W))"

  lemma losing_region_empty[simp]: "losing_region {}"
    unfolding losing_region_def strategy_of_def E_of_strat_def
    by auto

  (** The losing region exists in the graph *)
  lemma losing_region_in_V: "losing_region L \<Longrightarrow> L\<subseteq>V"
    unfolding losing_region_def by simp

  (** A single node is won by the player if the player has a strategy where all the cycles
      reachable from that node are won by the player *)
  definition won_by_player :: "'v \<Rightarrow> bool" where
    "won_by_player v \<equiv> (v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_player xs)))"

  (** A node that is won by the player is part of the graph *)
  lemma won_by_player_in_V: "won_by_player v \<Longrightarrow> v\<in>V"
    unfolding won_by_player_def by simp

  (** This definition exists for symmetry *)
  definition won_by_opponent :: "'v \<Rightarrow> bool" where
    "won_by_opponent v \<equiv> (v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>\<beta> \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_opponent xs)))"

  (** A vertex that is won by the opponent exists in the graph *)
  lemma won_by_opponent_in_V: "won_by_opponent v \<Longrightarrow> v\<in>V"
    unfolding won_by_opponent_def by simp

  (** Every node in a winning region for a player is won by that player *)
  lemma player_winning_region_won_by_player: "player_winning_region W \<Longrightarrow> \<forall>w\<in>W. won_by_player w"
    unfolding player_winning_region_def won_by_player_def by blast

  (** Every node in a losing region for a player is won by their opponent *)
  lemma losing_region_won_by_opponent: "losing_region W \<Longrightarrow> \<forall>w\<in>W. won_by_opponent w"
    unfolding losing_region_def won_by_opponent_def by blast

  (** If a node is won by the player, it cannot be won by the opponent *)
  lemma winning_v_exclusive: "won_by_player v \<Longrightarrow> \<not>won_by_opponent v"
    unfolding won_by_player_def won_by_opponent_def
  proof clarsimp
    fix \<sigma> \<sigma>'
    define G\<sigma> where "G\<sigma> = induced_subgraph (dom \<sigma>) \<sigma>"
    define G\<sigma>' where "G\<sigma>' = induced_subgraph (dom \<sigma>') \<sigma>'"
    assume \<sigma>_player: "strategy_of V\<^sub>\<alpha> \<sigma>"
      and \<sigma>_win: "\<forall>xs. cycle_from_node G\<sigma> v xs \<longrightarrow> winningP (top_pr xs)"
      and \<sigma>'_opp: "strategy_of (V-V\<^sub>\<alpha>) \<sigma>'"
      and "v\<in>V"
    interpret Ginter: paritygame "G\<sigma> \<inter> G\<sigma>'" V V\<^sub>0 pr
      using ind_subgraph_inter_opposed[OF G\<sigma>_def G\<sigma>'_def \<sigma>_player \<sigma>'_opp] .

    from Ginter.cycle_always_exists[OF \<open>v\<in>V\<close>] Ginter.succ \<open>v\<in>V\<close>
    obtain xs where xs: "cycle_from_node (G\<sigma> \<inter> G\<sigma>') v xs" by blast
    moreover from xs have "cycle_from_node G\<sigma> v xs" using cycle_from_node_inter by fastforce
    with \<sigma>_win have "winningP (top_pr xs)" by blast
    moreover from xs have "cycle_from_node G\<sigma>' v xs" using cycle_from_node_inter by fastforce
    ultimately show "\<exists>xs. cycle_from_node (G\<sigma>') v xs \<and> winning_player xs" by blast
  qed

  (** By the previous lemma, a node cannot be won by both players at the same time *)
  corollary "\<not>(won_by_player v \<and> won_by_opponent v)"
    using winning_v_exclusive by blast

  (** If a winning region is not empty, it cannot also be a losing region.
      Empty regions are technically won by both players. *)
  lemma nonempty_player_winning_region_exclusive:
    assumes "W \<noteq> {}"
    shows "player_winning_region W \<Longrightarrow> \<not>losing_region W"
  proof -
    assume "player_winning_region W"
    with assms obtain w where "w \<in> W" "won_by_player w"
      using player_winning_region_won_by_player by fast
    hence "\<not>won_by_opponent w" using winning_v_exclusive by simp
    from \<open>w\<in>W\<close> \<open>\<not>won_by_opponent w\<close> show "\<not>losing_region W"
      using losing_region_won_by_opponent by blast
  qed
end


(** Now that we have definitions for non-specific players, we need to introduce definitions for the
    actual players of parity games. *)
subsection \<open>Players\<close>
(** There are two players: Even and Odd. We need to identify them for future definitions *)
datatype player = EVEN | ODD

(** It is useful to be able to get the opponent of a player *)
fun opponent where
  "opponent EVEN = ODD"
| "opponent ODD = EVEN"

lemma opponent2[simp]: "opponent (opponent \<alpha>) = \<alpha>"
  by (cases \<alpha>) auto

(** Gives the player that would win a priority *)
definition player_wins_pr :: "nat \<Rightarrow> player" where
  "player_wins_pr p \<equiv> if even p then EVEN else ODD"

(** Gives the winning priority function for the players *)
fun player_winningP :: "player \<Rightarrow> nat \<Rightarrow> bool" where
  "player_winningP EVEN = even"
| "player_winningP ODD = odd"

context paritygame begin
  (** We can see a parity game as two player-specific parity games for either player *)
  sublocale P0: player_paritygame E V V\<^sub>0 pr V\<^sub>0 even
    apply unfold_locales
    by (auto simp: V\<^sub>0_in_V)

  sublocale P1: player_paritygame E V V\<^sub>0 pr V\<^sub>1 odd
    apply unfold_locales
    by (auto simp: V\<^sub>1_in_V)

  abbreviation player_wins_list :: "player \<Rightarrow> 'v list \<Rightarrow> bool" where
    "player_wins_list \<alpha> xs \<equiv> player_winningP \<alpha> (top_pr xs)"

  (** Gives the vertices belonging to a player *)
  fun V_player where
    "V_player EVEN = V\<^sub>0"
  | "V_player ODD = V\<^sub>1"

  (** Gives the vertices belonging to a player's opponent *)
  fun V_opponent where
    "V_opponent EVEN = V\<^sub>1"
  | "V_opponent ODD = V\<^sub>0"

  lemma V_player_opponent: "V_player (opponent \<alpha>) = V_opponent \<alpha>"
    by (cases \<alpha>) auto

  lemma V_opponent_opponent: "V_opponent (opponent \<alpha>) = V_player \<alpha>"
    by (cases \<alpha>) auto

  lemma V_diff_diff_V\<^sub>0: "(V - (V - V\<^sub>0)) = V\<^sub>0"
    by (simp add: V\<^sub>0_in_V double_diff)

  lemma V_player_opposite_V_opponent: "V_player \<alpha> = V - V_opponent \<alpha>"
    using V_diff_diff_V\<^sub>0 by (cases \<alpha>; simp add: V\<^sub>1_def)

  lemma V_opponent_opposite_V_player: "V_opponent \<alpha> = V - V_player \<alpha>"
      using V_diff_diff_V\<^sub>0 by (cases \<alpha>; simp add: V\<^sub>1_def)

  lemma V_opponent_player_int: "V' \<subseteq> V \<Longrightarrow> V' \<inter> V_opponent \<alpha> = V' - V_player \<alpha>"
    using V\<^sub>1_def by (cases \<alpha>) auto

  lemma v_notin_V_player_in_V_opponent: "v\<in>V \<Longrightarrow> v \<notin> V_player \<alpha> \<longleftrightarrow> v \<in> V_opponent \<alpha>"
    using V_player_opposite_V_opponent by auto

  (** Checks that a strategy belongs to a specific player *)
  definition strategy_of_player :: "player \<Rightarrow> 'v strat \<Rightarrow> bool" where
    "strategy_of_player \<alpha> \<sigma>= strategy_of (V_player \<alpha>) \<sigma>"

  lemma player_strat_dom: "strategy_of_player \<alpha> \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> V_player \<alpha>"
    unfolding strategy_of_player_def strategy_of_def by simp

  lemma player_strat_in_E: "strategy_of_player \<alpha> \<sigma> \<Longrightarrow> E_of_strat \<sigma> \<subseteq> E"
    unfolding strategy_of_player_def strategy_of_def by simp


  subsubsection \<open>Winning for Players\<close>
  (** Specifies winning regions for the players *)
  fun winning_region where
    "winning_region EVEN = P0.player_winning_region"
  | "winning_region ODD = P1.player_winning_region"

  lemma winning_region_empty[simp]: "winning_region \<alpha> {}"
    by (cases \<alpha>; simp)

  (** A winning region is part of the graph *)
  lemma winning_region_in_V: "winning_region \<alpha> W \<Longrightarrow> W\<subseteq>V"
    using P0.player_winning_region_in_V P1.player_winning_region_in_V by (cases \<alpha>) auto

  (** The player has a strategy under which their winning region is closed and all cycles reachable
      from nodes in the region are won by the player *)
  lemma winning_region_strat: "winning_region \<alpha> W = (W\<subseteq>V \<and> (\<exists>\<sigma>.
    strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = V_player \<alpha> \<inter> W \<and> ran \<sigma> \<subseteq> W \<and>
    (\<forall>w\<in>W. \<forall>xs. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) w xs \<longrightarrow> player_wins_list \<alpha> xs) \<and>
    E `` (W \<inter> V_opponent \<alpha>) \<subseteq> W))"
    unfolding strategy_of_player_def
    using P0.player_winning_region_def P1.player_winning_region_def V\<^sub>1_def V\<^sub>0_opposite_V\<^sub>1 by (cases \<alpha>; simp)

  (** A player can win a node *)
  fun won_by where
    "won_by EVEN = P0.won_by_player"
  | "won_by ODD = P1.won_by_player"

  (** If a node is won by a player, it is part of the game *)
  lemma won_by_in_V: "won_by \<alpha> v \<Longrightarrow> v\<in>V"
    using P0.won_by_player_in_V P1.won_by_player_in_V by (cases \<alpha>) auto

  (** We can get a winning strategy for a node that is won by a player *)
  lemma won_by_strat: "won_by \<alpha> v = (v \<in> V \<and> (\<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) v xs \<longrightarrow> player_wins_list \<alpha> xs)))"
    unfolding strategy_of_player_def
    by (cases \<alpha>; simp add: P0.won_by_player_def P1.won_by_player_def)

  (** The winning and losing regions are symmetrical for the two sublocales *)
  lemma losing_region_simps[simp]:
    "P1.losing_region = P0.player_winning_region"
    "P0.losing_region = P1.player_winning_region"
    unfolding P0.losing_region_def P1.losing_region_def
    unfolding P0.player_winning_region_def P1.player_winning_region_def
    unfolding V\<^sub>1_def
    by (auto simp: V_diff_diff_V\<^sub>0)

  lemma won_by_opponent_simps[simp]:
    "P1.won_by_opponent = P0.won_by_player"
    "P0.won_by_opponent = P1.won_by_player"
    unfolding P0.won_by_opponent_def P1.won_by_opponent_def P0.won_by_player_def P1.won_by_player_def
    unfolding V\<^sub>1_def
    by (auto simp: V_diff_diff_V\<^sub>0)

  (** If a node is in a player's winning region, it is won by that player *)
  lemma winning_region_won_by: "\<lbrakk>winning_region \<alpha> W; v\<in>W\<rbrakk> \<Longrightarrow> won_by \<alpha> v"
    using P0.player_winning_region_won_by_player P1.player_winning_region_won_by_player by (cases \<alpha>) auto

  (** If a player's winning region is non-empty, it is not a winning region for their opponent *)
  lemma nonempty_winning_region_not_winning_for_opponent:
    assumes "W \<noteq> {}"
    shows "winning_region \<alpha> W \<Longrightarrow> \<not>winning_region (opponent \<alpha>) W"
    using assms P0.nonempty_player_winning_region_exclusive P1.nonempty_player_winning_region_exclusive
    by (cases \<alpha>) auto

  (** A node cannot be won by a player and their opponent at the same time. *)
  lemma won_by_player_not_won_by_opponent: "\<not>(won_by \<alpha> v \<and> won_by (opponent \<alpha>) v)"
    using P0.winning_v_exclusive P1.winning_v_exclusive by (cases \<alpha>) auto
end (** End of context paritygame *)

end
