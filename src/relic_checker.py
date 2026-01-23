from source_data_handler import SourceDataHandler
from globals import RELIC_GROUPS
from enum import IntEnum, auto, unique
from typing import Optional, Union


@unique
class InvalidReason(IntEnum):
    VALIDATION_ERROR = -1
    NONE = 0
    IN_ILLEGAL_RANGE = auto()
    INVALID_ITEM = auto()
    EFF_MUST_EMPTY = auto()
    EFF_NOT_IN_ROLLABLE_POOL = auto()
    EFF_CONFLICT = auto()

    CURSE_MUST_EMPTY = auto()
    CURSE_REQUIRED_BY_EFFECT = auto()
    CURSE_NOT_IN_ROLLABLE_POOL = auto()
    CURSE_CONFLICT = auto()
    CURSES_NOT_ENOUGH = auto()

    EFFS_NOT_SORTED = auto()


def is_curse_invalid(reason: int):
    return reason in [
        InvalidReason.CURSE_MUST_EMPTY,
        InvalidReason.CURSE_REQUIRED_BY_EFFECT,
        InvalidReason.CURSE_NOT_IN_ROLLABLE_POOL,
        InvalidReason.CURSE_CONFLICT,
        InvalidReason.CURSES_NOT_ENOUGH
    ]


class RelicChecker:
    RELIC_RANGE: tuple[int, int] = (100, 2013322)
    UNIQUENESS_IDS: set[int] = \
        set(i for i in range(RELIC_GROUPS['unique_1'][0],
                             RELIC_GROUPS['unique_1'][1] + 1)) |\
        set(i for i in range(RELIC_GROUPS['unique_2'][0],
                             RELIC_GROUPS['unique_2'][1] + 1))

    def __init__(self, ga_relic, data_source: SourceDataHandler):
        self.ga_relic = ga_relic
        self.data_source = data_source
        self.illegal_gas = []
        self.curse_illegal_gas = []  # Track relics illegal due to missing curses

    def check_possible_effects_seq(self, relic_id: int, effects: list[int],
                                   stop_on_valid: bool = False) -> list[tuple[tuple[int, int, int], list[InvalidReason]]]:
        """
        Check that all relic effects are in the relic effects pool with all possible sequences. 
        
        :param relic_id: The relic ID to check
        :type relic_id: int
        :param effects: List of 6 effect IDs [e1, e2, e3, curse1, curse2, curse3]
        :type effects: list[int]
        :param stop_on_valid: If True, stop checking after finding the first valid sequence
        :type stop_on_valid: bool, optional
        :return: List of tuples containing the effect sequence and corresponding invalid reasons
        :rtype: list[tuple[tuple[int, int, int], list[InvalidReason]]]
        """
        # Load relic effects pool data
        try:
            pools = self.data_source.get_relic_pools_seq(relic_id)
        except KeyError:
            return [((-1, -1, -1), [InvalidReason.VALIDATION_ERROR])]
        # There are 6 effects: 3 normal effects and 3 curse effects
        # The first 3 are normal effects, the last 3 are curse effects
        # Each effect corresponds to a pool ID
        # If pool ID is -1, the effect must be empty (4294967295)
        # If pool ID is not -1, the effect must be in the pool
        # Try all possible sequences of effects
        # Because we don't know the original order of effects
        possible_sequences = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0],
                              [2, 0, 1], [2, 1, 0]]
        test_results = []
        for seq in possible_sequences:
            cur_effects = [effects[i] for i in seq]
            cur_curses = [effects[i+3] for i in seq]
            test_result = []

            # Check effects (indices 0-2)
            for idx in range(3):
                eff = cur_effects[idx]
                if pools[idx] == -1:
                    if eff not in [-1, 0, 4294967295]:  # Must be empty
                        test_result.append(InvalidReason.EFF_MUST_EMPTY)
                    else:
                        test_result.append(InvalidReason.NONE)
                else:
                    if eff not in self.data_source.get_pool_rollable_effects(pools[idx]):
                        # Effect must have non-zero weight in the pool to be valid
                        test_result.append(InvalidReason.EFF_NOT_IN_ROLLABLE_POOL)
                    else:
                        test_result.append(InvalidReason.NONE)

            # Check curses (indices 3-5)
            for idx in range(3):
                curse = cur_curses[idx]
                eff = cur_effects[idx]
                curse_pool = pools[idx + 3]

                if curse_pool == -1:
                    # No curse slot - curse must be empty
                    if curse not in [-1, 0, 4294967295]:
                        test_result.append(InvalidReason.CURSE_MUST_EMPTY)
                    else:
                        test_result.append(InvalidReason.NONE)
                else:
                    # Curse slot exists
                    if curse in [-1, 0, 4294967295]:
                        # Empty curse - check if effect needs one
                        effect_needs = self._effect_needs_curse(eff)
                        if effect_needs:
                            test_result.append(InvalidReason.CURSE_REQUIRED_BY_EFFECT)
                        else:
                            test_result.append(InvalidReason.NONE)
                    elif curse not in self.data_source.get_pool_rollable_effects(curse_pool):
                        # Curse must have non-zero weight in the pool
                        test_result.append(InvalidReason.CURSE_NOT_IN_ROLLABLE_POOL)
                    else:
                        test_result.append(InvalidReason.NONE)

            test_results.append((tuple(seq), test_result))
            if stop_on_valid and all(r == InvalidReason.NONE for r in test_results[-1][1]):
                return test_results
        return test_results

    def _check_relic_effects_in_pool(self, relic_id: int, effects: list[int]) -> tuple[InvalidReason, int]:
        """
        Check that all relic effects are in the relic effects pool.

        Args:
            relic_id: The relic ID to check
            effects: List of 6 effect IDs [e1, e2, e3, curse1, curse2, curse3]
        
        Return:
            A tuple containing:
            - InvalidReason: The invalid reason if any, or InvalidReason.NONE if valid
            - int: The index of the first invalid effect (0-based), or -1 if not applicable
        """
        # Try all possible sequences of effects and break on first valid
        test_results = self.check_possible_effects_seq(relic_id, effects, stop_on_valid=True)
        if not test_results:
            # This should not happen if check_possible_effects_seq is implemented correctly
            # as it should always return at least one result, even if invalid.
            return InvalidReason.VALIDATION_ERROR, -1
        elif test_results[0][1] == InvalidReason.VALIDATION_ERROR:
            return InvalidReason.VALIDATION_ERROR, -1
        # Get the last test result (the valid one if any)
        _, test_result = test_results[-1]
        if all(r == InvalidReason.NONE for r in test_result):
            return InvalidReason.NONE, 0
        # Find the first invalid reason in the first invalid sequence
        # If any sequence is valid, we would have returned above
        _, first_invalid_result = test_results[0]
        for idx, res in enumerate(first_invalid_result):
            if res == InvalidReason.NONE:
                continue
            return res, idx
        return InvalidReason.VALIDATION_ERROR, -1

    def _effect_needs_curse(self, effect_id: int) -> bool:
        """Check if an effect REQUIRES a curse.

        An effect needs a curse if it ONLY exists in pool 2000000 (which is always
        paired with curse_pool 3000000) and not in pools 2100000 or 2200000
        (which have no curse requirement) or any regular pools.
        """
        return self.data_source.effect_needs_curse(effect_id)

    def check_curse_invalidity(self, relic_id: int, effects: list[int]):
        """This method is merged into _check_invalidity
        """
        pass

    def check_invalidity(self, relic_id: int, effects: list[int],
                         return_1st_invalid_idx: bool = False) -> Union[
                             InvalidReason, tuple[InvalidReason, int]]:
        """
        Check if a relic is invalid based on several rules.
        
        Args:
            relic_id (int): The relic ID to check.
            effects (list[int]): List of 6 effect IDs [e1, e2, e3, curse1, curse2, curse3].
            return_1st_invalid_idx (bool, optional): Whether to output the errored effects list index (0-based),
            where -1 indicates the error is unrelated to the effect's position. Defaults to False.

        Returns:
            InvalidReason | tuple[InvalidReason, int]: InvalidReason or InvalidReason and first invalid effect index.
        """

        # Rule 1
        if relic_id in range(RELIC_GROUPS['illegal'][0],
                             RELIC_GROUPS['illegal'][1] + 1):
            if return_1st_invalid_idx:
                return InvalidReason.IN_ILLEGAL_RANGE, -1
            else:
                return InvalidReason.IN_ILLEGAL_RANGE

        # Rule 2

        if relic_id not in range(self.RELIC_RANGE[0],
                                 self.RELIC_RANGE[1]+1):
            if return_1st_invalid_idx:
                return InvalidReason.INVALID_ITEM, -1
            else:
                return InvalidReason.INVALID_ITEM
        else:
            # Rule: Effects must be in valid pools for this relic
            # This is the primary validation - effects must match the relic's effect pools
            effects_valid, first_invalid_idx = \
                self._check_relic_effects_in_pool(relic_id, effects)
            if effects_valid != InvalidReason.NONE:
                if return_1st_invalid_idx:
                    return effects_valid, first_invalid_idx
                else:
                    return effects_valid

            # Rule: Deep-only effects must have curses
            # Effects that only exist in deep relic pools require curses
            # when used on multi-effect relics
            deep_only_effects = sum(1 for eff in effects[:3]
                                    if self._effect_needs_curse(eff))
            curses_provided = sum(1 for c in effects[3:]
                                  if c not in [-1, 0, 4294967295])
            # Quick check: if not enough curses for deep-only effects
            if deep_only_effects > curses_provided:
                # Not enough curses for deep-only effects
                if return_1st_invalid_idx:
                    return InvalidReason.CURSES_NOT_ENOUGH, -1
                else:
                    return InvalidReason.CURSES_NOT_ENOUGH
            # if self.check_curse_invalidity(relic_id, effects):
            #     return True

            # Rule: The compatibilityId (conflict ID) should not be duplicated.
            conflict_ids = []
            for idx, effect_id in enumerate(effects):
                # Skip empty effects
                if effect_id in [-1, 0, 4294967295]:
                    continue
                conflict_id = \
                    self.data_source.get_effect_conflict_id(effect_id)
                # conflict id -1 is allowed to be duplicated
                if conflict_id in conflict_ids and conflict_id != -1:
                    if return_1st_invalid_idx:
                        return (InvalidReason.EFF_CONFLICT, idx) if idx < 3 else (InvalidReason.CURSE_CONFLICT, idx)
                    else:
                        return InvalidReason.EFF_CONFLICT if idx < 3 else InvalidReason.CURSE_CONFLICT
                conflict_ids.append(conflict_id)
            # Rule: Effect order
            # Effects are sorted in ascending order by overrideEffectId.
            # If overrideEffectId values are identical,
            # compare the effect IDs themselves.
            # Sorting considers only the top three positive effects.
            # Curse effects are bound to their corresponding positive effects.
            sort_ids = []
            for effect_id in effects[:3]:
                # Skip empty effects
                if effect_id in [-1, 0, 4294967295]:
                    sort_ids.append(float('inf'))
                else:
                    sort_id = self.data_source.get_sort_id(effect_id)
                    sort_ids.append(sort_id)
            sort_tuple = zip(sort_ids, effects[:3])
            sorted_effects = sorted(sort_tuple, key=lambda x: (x[0], x[1]))
            for i in range(len(sorted_effects)):
                if sorted_effects[i][1] != effects[i]:
                    if return_1st_invalid_idx:
                        return InvalidReason.EFFS_NOT_SORTED, -1
                    else:
                        return InvalidReason.EFFS_NOT_SORTED
            if return_1st_invalid_idx:
                return InvalidReason.NONE, -1
            return InvalidReason.NONE

    def is_strict_invalid(self, relic_id: int, effects: list[int], invalid_reason: Optional[InvalidReason] = None):
        """Check if a relic has effects with 0 weight in the relic's specific pools,
        but non-zero weight in other pools of the same type.

        This catches cases where an effect could exist on a deep relic (weight > 0 in
        some deep pool) but has 0 weight in the specific pool assigned to this relic,
        AND no permutation exists where all effects have non-zero weight in their slot's pool.

        Returns True only if NO permutation results in all effects being strictly valid
        for their permuted slot's specific pool.
        """
        # Skip if relic is actually illegal (that's a different issue)
        if not invalid_reason and invalid_reason != InvalidReason.NONE:
            invalid_reason = self.check_invalidity(relic_id, effects)
        if invalid_reason != InvalidReason.NONE:
            return False

        try:
            pools = self.data_source.get_relic_pools_seq(relic_id)
        except KeyError:
            return False

        deep_pools = {2000000, 2100000, 2200000}

        # Check if this relic uses any deep pools
        has_deep_pools = any(p in deep_pools for p in pools[:3])
        if not has_deep_pools:
            return False

        # Try all permutations - if ANY permutation is strictly valid, return False
        possible_sequences = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

        for seq in possible_sequences:
            cur_effects = [effects[i] for i in seq]
            sequence_strict_valid = True

            for idx in range(3):
                effect = cur_effects[idx]
                effect_pool = pools[idx]

                # Skip empty effects
                if effect in [-1, 0, 4294967295]:
                    continue

                # Skip non-deep pools
                if effect_pool not in deep_pools:
                    continue

                # Check if effect has non-zero weight in this SPECIFIC pool
                specific_pool_effects = self.data_source.get_pool_effects_strict(effect_pool)

                if effect not in specific_pool_effects:
                    sequence_strict_valid = False
                    break

            if sequence_strict_valid:
                # Found a permutation where all effects are strictly valid
                return False

        # No permutation is strictly valid
        return True

    def get_strict_invalid_reason(self, relic_id: int, effects: list[int]) -> str | None:
        """Get a human-readable reason why a relic is strictly invalid.

        Returns None if the relic is not strictly invalid.
        """
        if not self.is_strict_invalid(relic_id, effects, InvalidReason.NONE):
            return None

        try:
            pools = self.data_source.get_relic_pools_seq(relic_id)
        except KeyError:
            return "Unknown relic ID"

        deep_pools = {2000000, 2100000, 2200000}
        pool_names = {2000000: "Pool A", 2100000: "Pool B", 2200000: "Pool C"}

        # Find which effects are problematic
        problematic_effects = []
        for i, effect in enumerate(effects[:3]):
            if effect in [-1, 0, 4294967295]:
                continue

            effect_pool = pools[i]
            if effect_pool not in deep_pools:
                continue

            # Check if effect is strictly valid in this pool
            specific_pool_effects = self.data_source.get_pool_effects_strict(effect_pool)
            if effect not in specific_pool_effects:
                # Find which pools this effect IS valid in
                valid_pools = []
                for pool_id in deep_pools:
                    if effect in self.data_source.get_pool_effects_strict(pool_id):
                        valid_pools.append(pool_names.get(pool_id, str(pool_id)))

                effect_name = self.data_source.get_effect_name(effect)
                if valid_pools:
                    problematic_effects.append(
                        f"'{effect_name}' needs {'/'.join(valid_pools)} but slot {i+1} uses {pool_names.get(effect_pool, str(effect_pool))}"
                    )
                else:
                    problematic_effects.append(
                        f"'{effect_name}' has 0 weight in all deep pools"
                    )

        if not problematic_effects:
            return "No valid permutation exists"

        return "; ".join(problematic_effects)

    def sort_effects(self, effects: list[int]):
        """Sort effects by their sort ID, keeping curses paired with their primary effects.

        Effects structure: [effect1, effect2, effect3, curse1, curse2, curse3]
        After sorting, curse at position i always corresponds to effect at position i.
        """
        # Build list of (sort_id, effect_id, curse_id) tuples
        effect_curse_pairs = []
        curses = effects[3:]
        curse_tuples = []
        for idx in range(3):
            curse_id = curses[idx]
            if curse_id in [-1, 0, 4294967295]:
                sort_id = float('inf')  # Empty curses go last
            else:
                sort_id = self.data_source.get_sort_id(curse_id)
            curse_tuples.append((sort_id, curse_id))
        curse_tuples = sorted(curse_tuples, key=lambda x: (x[0], x[1]))
        curses = [pair[1] for pair in curse_tuples]

        for idx in range(3):
            effect_id = effects[idx]
            curse_id = 4294967295
            if self.data_source.effect_needs_curse(effect_id):
                curse_id = curses.pop(0)
            else:
                curse_id = curses.pop()

            # Get sort ID for the primary effect
            if effect_id in [-1, 0, 4294967295]:
                sort_id = float('inf')  # Empty effects go last
            else:
                sort_id = self.data_source.get_sort_id(effect_id)

            effect_curse_pairs.append((sort_id, effect_id, curse_id))

        # Sort by (sort_id, effect_id) - effect_id as tiebreaker
        sorted_pairs = sorted(effect_curse_pairs, key=lambda x: (x[0], x[1]))

        # Build result: sorted effects followed by their corresponding curses
        result = [pair[1] for pair in sorted_pairs]  # effects
        result.extend([pair[2] for pair in sorted_pairs])  # curses
        return result

    def has_valid_order(self, relic_id: int, effects: list[int]) -> bool:
        """Check if ANY permutation of effects is valid for this relic.

        This uses get_pool_rollable_effects (effects with >0 weight).
        Used to detect if reordering alone could fix an illegal relic.
        """
        try:
            pools = self.data_source.get_relic_pools_seq(relic_id)
        except KeyError:
            return False

        possible_sequences = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

        for seq in possible_sequences:
            cur_effects = [effects[i] for i in seq]
            cur_curses = [effects[i + 3] for i in seq]
            sequence_valid = True

            for idx in range(3):
                effect = cur_effects[idx]
                curse = cur_curses[idx]
                effect_pool = pools[idx]
                curse_pool = pools[idx + 3]

                # Skip empty effects
                if effect in [-1, 0, 4294967295]:
                    continue

                # Check effect is rollable in pool (must have >0 weight)
                pool_effects = self.data_source.get_pool_rollable_effects(effect_pool)
                if effect not in pool_effects:
                    sequence_valid = False
                    break

                # Check curse requirements
                if self.data_source.effect_needs_curse(effect):
                    if curse_pool == -1:
                        sequence_valid = False
                        break
                    # Curse must be present and valid
                    if curse in [-1, 0, 4294967295]:
                        sequence_valid = False
                        break
                    pool_curses = self.data_source.get_pool_rollable_effects(curse_pool)
                    if curse not in pool_curses:
                        sequence_valid = False
                        break

                # Check curse placement (if curse present but effect doesn't need it)
                if curse not in [-1, 0, 4294967295]:
                    if curse_pool == -1:
                        sequence_valid = False
                        break
                    pool_curses = self.data_source.get_pool_rollable_effects(curse_pool)
                    if curse not in pool_curses:
                        sequence_valid = False
                        break

            if sequence_valid:
                return True

        return False

    def get_valid_order(self, relic_id: int, effects: list[int]):
        """Find a permutation of effects that is valid for this relic.

        Returns the reordered effects list if a valid permutation exists,
        or None if no permutation can make the relic valid.
        This checks rollable pool validity (effects must have non-zero weight).
        """
        try:
            pools = self.data_source.get_relic_pools_seq(relic_id)
        except KeyError:
            return None

        possible_sequences = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

        for seq in possible_sequences:
            cur_effects = [effects[i] for i in seq]
            cur_curses = [effects[i + 3] for i in seq]
            sequence_valid = True

            for idx in range(3):
                effect = cur_effects[idx]
                curse = cur_curses[idx]
                effect_pool = pools[idx]
                curse_pool = pools[idx + 3]

                # Skip empty effects
                if effect in [-1, 0, 4294967295]:
                    continue

                # Check effect is rollable in the pool (must have non-zero weight)
                pool_effects = self.data_source.get_pool_rollable_effects(effect_pool)
                if effect not in pool_effects:
                    sequence_valid = False
                    break

                # Check curse requirements
                if self.data_source.effect_needs_curse(effect):
                    if curse_pool == -1:
                        sequence_valid = False
                        break
                    # Curse must be present and valid
                    if curse in [-1, 0, 4294967295]:
                        sequence_valid = False
                        break
                    pool_curses = self.data_source.get_pool_rollable_effects(curse_pool)
                    if curse not in pool_curses:
                        sequence_valid = False
                        break

                # Check curse placement (if curse present but effect doesn't need it)
                if curse not in [-1, 0, 4294967295]:
                    if curse_pool == -1:
                        sequence_valid = False
                        break
                    pool_curses = self.data_source.get_pool_rollable_effects(curse_pool)
                    if curse not in pool_curses:
                        sequence_valid = False
                        break

            if sequence_valid:
                # Found a valid permutation - return effects sorted for storage
                return self.sort_effects(effects)

        return None

    def get_strictly_valid_order(self, relic_id: int, effects: list[int]):
        """Find a permutation of effects that is strictly valid for this relic.

        Returns the reordered effects list if a valid permutation exists,
        or None if no permutation can make the relic strictly valid.
        This requires effects to have non-zero weight in the specific pool, not just combined.
        """
        try:
            pools = self.data_source.get_relic_pools_seq(relic_id)
        except KeyError:
            return None

        deep_pools = {2000000, 2100000, 2200000}
        possible_sequences = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

        for seq in possible_sequences:
            cur_effects = [effects[i] for i in seq]
            cur_curses = [effects[i + 3] for i in seq]
            sequence_strict_valid = True

            for idx in range(3):
                effect = cur_effects[idx]
                curse = cur_curses[idx]
                effect_pool = pools[idx]
                curse_pool = pools[idx + 3]

                # Check effect is valid in the pool (any pool, not just deep)
                pool_effects = self.data_source.get_pool_effects_strict(effect_pool)
                if effect not in pool_effects and (pool_effects or effect not in [-1, 0, 4294967295]):
                    sequence_strict_valid = False
                    break

                # Check curse requirements
                if self.data_source.effect_needs_curse(effect):
                    if curse_pool == -1:
                        sequence_strict_valid = False
                        break
                    # Curse must be present and valid
                    if curse in [-1, 0, 4294967295]:
                        sequence_strict_valid = False
                        break
                    pool_curses = self.data_source.get_pool_effects_strict(curse_pool)
                    if curse not in pool_curses:
                        sequence_strict_valid = False
                        break

                # Check curse placement (if curse present but effect doesn't need it)
                if curse not in [-1, 0, 4294967295]:
                    if curse_pool == -1:
                        sequence_strict_valid = False
                        break

            if sequence_strict_valid:
                # Found a valid permutation - return effects sorted for storage
                return self.sort_effects(effects)

        return None

    def find_replacement_effect(self, relic_id: int, slot_idx: int, current_effect: int):
        """Find a replacement effect that is strictly valid in the given slot.

        Returns a list of (effect_id, effect_name) tuples that could replace
        the current effect while being strictly valid in the slot's pool.
        """
        try:
            pools = self.data_source.get_relic_pools_seq(relic_id)
        except KeyError:
            return []

        effect_pool = pools[slot_idx]
        curse_pool = pools[slot_idx + 3]

        if effect_pool == -1:
            return []

        # Get effects that are strictly valid in this pool
        strict_effects = self.data_source.get_pool_effects_strict(effect_pool)

        # Filter based on curse requirements
        valid_replacements = []
        for eff_id in strict_effects:
            if eff_id == current_effect:
                continue  # Skip current effect

            needs_curse = self.data_source.effect_needs_curse(eff_id)

            # If effect needs curse, slot must have curse_pool
            if needs_curse and curse_pool == -1:
                continue

            eff_name = self.data_source.effect_name(eff_id)
            valid_replacements.append((eff_id, eff_name))

        return valid_replacements

    def set_illegal_relics(self):
        illegal_relics = []
        curse_illegal_relics = []
        strict_invalid_relics = []
        relic_group_by_id = {}
        for relic in self.ga_relic:
            ga, relic_id, e1, e2, e3, e4, e5, e6, offset, size = relic
            real_id = relic_id - 2147483648
            if str(real_id) not in relic_group_by_id.keys():
                relic_group_by_id[str(real_id)] = []
            relic_group_by_id[str(real_id)].append(relic)
            effects = [e1, e2, e3, e4, e5, e6]
            invalid_reason = self.check_invalidity(real_id, effects)
            if invalid_reason != InvalidReason.NONE:
                illegal_relics.append(ga)
                # Check if it's specifically curse-illegal
                if is_curse_invalid(invalid_reason):
                    curse_illegal_relics.append(ga)
            elif self.is_strict_invalid(real_id, effects, InvalidReason.NONE):
                # Valid but has effects with 0 weight in specific pool
                strict_invalid_relics.append(ga)

        for real_id, relics in relic_group_by_id.items():
            if int(real_id) in self.UNIQUENESS_IDS:
                if len(relics) > 1:
                    legal_found = False
                    for relic in relics:
                        (ga, relic_id,
                         e1, e2, e3, e4, e5, e6,
                         offset, size) = relic
                        if ga in illegal_relics:
                            continue
                        if not legal_found:
                            legal_found = True
                            continue
                        illegal_relics.append(ga)
        self.illegal_gas = illegal_relics
        self.curse_illegal_gas = curse_illegal_relics
        self.strict_invalid_gas = strict_invalid_relics

    @property
    def illegal_count(self):
        return len(self.illegal_gas)

    def append_illegal(self, ga, is_curse_illegal=False):
        if ga not in self.illegal_gas:
            self.illegal_gas.append(ga)
        if is_curse_illegal and ga not in self.curse_illegal_gas:
            self.curse_illegal_gas.append(ga)

    def remove_illegal(self, ga):
        if ga in self.illegal_gas:
            self.illegal_gas.remove(ga)
        if ga in self.curse_illegal_gas:
            self.curse_illegal_gas.remove(ga)
        if ga in self.strict_invalid_gas:
            self.strict_invalid_gas.remove(ga)

    def update_illegal(self, ga_handle, item_id, source_effects):
        invalid_reason = self.check_invalidity(item_id, source_effects)
        if invalid_reason and ga_handle not in self.illegal_gas:
            self.append_illegal(ga_handle, is_curse_invalid(invalid_reason))
        elif not invalid_reason and ga_handle in self.illegal_gas:
            self.remove_illegal(ga_handle)
        if self.is_strict_invalid(item_id, source_effects, invalid_reason):
            if ga_handle not in self.strict_invalid_gas:
                self.strict_invalid_gas.append(ga_handle)
        else:
            if ga_handle in self.strict_invalid_gas:
                self.strict_invalid_gas.remove(ga_handle)

    def find_id_range(self, relic_id: int):
        for group_name, group_range in RELIC_GROUPS.items():
            if relic_id in range(group_range[0], group_range[1] + 1):
                return group_name, group_range
        return None

    @staticmethod
    def is_deep_relic(relic_id: int):
        return SourceDataHandler.is_deep_relic(relic_id)
