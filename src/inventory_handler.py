import struct
from typing import Literal
from relic_checker import RelicChecker, InvalidReason, is_curse_invalid
from source_data_handler import SourceDataHandler
from globals import ITEM_TYPE_RELIC, ITEM_TYPE_WEAPON, ITEM_TYPE_ARMOR, UNIQUENESS_IDS
import globals
import logging
import threading
import pandas as pd


logger = logging.getLogger(__name__)


def remove_padding_area():
    # Remove 72 bytes from the padding area at the end of the file.
    # Note: Why 72 Bytes? Because empty Item State use 8 Bytes, And Relic Item State Use 80 Bytes.
    # The save file must maintain a constant size for the game to load it.
    globals.data = globals.data[: -0x1C - 72] + globals.data[-0x1C:]


def insert_padding_area():
    # Insert 72 bytes of padding at the end of the file.
    # The save file must maintain a constant size for the game to load it.
    globals.data = globals.data[: -0x1C] + b'\x00' * 72 + globals.data[-0x1C:]


class ItemState:
    BASE_SIZE = 8

    def __init__(self):
        self.ga_handle = 0
        self.instance_id = 0
        self.item_id = 0xffffffff
        self.real_item_id = 0x00ffffff
        self.type_bits = 0
        self.data: bytearray = bytes.fromhex('00000000FFFFFFFF')
        self.size = 8
        self.index = -1

    @classmethod
    def create_dummy_relic(cls, instance_id, relic_type: str = "normal"):
        if relic_type.lower() == "normal":
            real_item_id = 100
            item_id = 0x80000000 | (real_item_id & 0x00FFFFFF)
            dummy_effect_id = 7000000
        elif relic_type.lower() == "deep":
            real_item_id = 2003000
            item_id = 0x80000000 | (real_item_id & 0x00FFFFFF)
            dummy_effect_id = 7001002
        else:
            raise ValueError("Invalid relic type")
        dummy_relic = cls()
        dummy_relic.ga_handle = 0xC0000000 | (instance_id & 0x00FFFFFF)
        dummy_relic.item_id = item_id
        dummy_relic.instance_id = instance_id
        dummy_relic.real_item_id = real_item_id
        dummy_relic.type_bits = ITEM_TYPE_RELIC
        dummy_relic.size = 80
        _padding = bytes([
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0xFF,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF
        ])

        _data: bytearray = bytearray(80)
        struct.pack_into("<I", _data, 0, dummy_relic.ga_handle)  # ga_handle
        struct.pack_into("<I", _data, 4, dummy_relic.item_id)  # item_id : real_id->100 Delicate Burning Scene/id->2003000 Deep Delicate Burning Scene
        struct.pack_into("<I", _data, 8, dummy_relic.item_id)  # durability (same as item_id when item is a relic)
        struct.pack_into("<I", _data, 12, int(0xffffffff))  # unk_1
        struct.pack_into("<I", _data, 16, int(dummy_effect_id))  # effect_1:Normal-> Vigor + 1(id: 7000000) / Deep -> Poise +3(id:7001002)
        struct.pack_into("<I", _data, 20, int(0xffffffff))  # effect_2
        struct.pack_into("<I", _data, 24, int(0xffffffff))  # effect_3
        _data = _data[:28] + _padding + _data[28+len(_padding):]  # add padding
        struct.pack_into("<I", _data, 56, int(0xffffffff))  # curse_1
        struct.pack_into("<I", _data, 60, int(0xffffffff))  # curse_2
        struct.pack_into("<I", _data, 64, int(0xffffffff))  # curse_3
        struct.pack_into("<I", _data, 68, int(0xffffffff))  # unk_2
        struct.pack_into("<Q", _data, 72, int(0))  # 8 bytes end_padding

        dummy_relic.data = _data
        return dummy_relic

    def from_bytes(self, user_data: bytearray, offset=0):
        data_len = len(user_data)

        # Check if we have enough data for the base read
        if offset + self.BASE_SIZE > data_len:
            raise ValueError("Invalid data length. Save File may be corrupted.")

        self.ga_handle, self.item_id = struct.unpack_from("<II", user_data, offset)
        self.type_bits = self.ga_handle & 0xF0000000
        self.instance_id = self.ga_handle & 0x00FFFFFF
        self.real_item_id = self.item_id & 0x00FFFFFF
        cursor = offset

        if self.ga_handle != 0:
            if self.type_bits == ITEM_TYPE_WEAPON:
                if cursor + 88 > data_len:
                    raise ValueError("Invalid data length. Save File may be corrupted.")
                self.size = 88
                self.data = user_data[cursor:cursor+self.size]
            elif self.type_bits == ITEM_TYPE_ARMOR:
                if cursor + 16 > data_len:
                    raise ValueError("Invalid data length. Save File may be corrupted.")
                self.size = 16
                self.data = user_data[cursor:cursor+self.size]
            elif self.type_bits == ITEM_TYPE_RELIC:
                if cursor + 80 > data_len:
                    raise ValueError("Invalid data length. Save File may be corrupted.")
                self.size = 80
                self.data = user_data[cursor:cursor+self.size]

    def set_real_id(self, real_id):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Real ID can only be set for relics")
        self.real_item_id = real_id
        self.item_id = self.real_item_id | 0x80000000
        struct.pack_into("<I", self.data, 4, self.item_id)
        self.durability = self.item_id

    @property
    def relic(self):
        assert self.type_bits == ITEM_TYPE_RELIC
        return SourceDataHandler().relics[self.real_item_id]

    @property
    def name(self) -> str:
        assert self.type_bits == ITEM_TYPE_RELIC
        return self.relic.name

    @property
    def is_unique(self):
        assert self.type_bits == ITEM_TYPE_RELIC
        return self.real_item_id in UNIQUENESS_IDS

    @property
    def is_deep(self) -> bool:
        assert self.type_bits == ITEM_TYPE_RELIC
        return self.relic.is_deep()

    @property
    def durability(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 8)[0]

    @durability.setter
    def durability(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Durability can only be set for relics")
        struct.pack_into("<I", self.data, 8, value)

    @property
    def unk_1(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 12)[0]

    @unk_1.setter
    def unk_1(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Unk_1 can only be set for relics")
        struct.pack_into("<I", self.data, 12, value)

    @property
    def effect_1(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 16)[0]

    @effect_1.setter
    def effect_1(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Effect_1 can only be set for relics")
        struct.pack_into("<I", self.data, 16, value)

    @property
    def effect_2(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 20)[0]

    @effect_2.setter
    def effect_2(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Effect_2 can only be set for relics")
        struct.pack_into("<I", self.data, 20, value)

    @property
    def effect_3(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 24)[0]

    @effect_3.setter
    def effect_3(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Effect_3 can only be set for relics")
        struct.pack_into("<I", self.data, 24, value)

    @property
    def curse_1(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 56)[0]

    @curse_1.setter
    def curse_1(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Curse_1 can only be set for relics")
        struct.pack_into("<I", self.data, 56, value)

    @property
    def curse_2(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 60)[0]

    @curse_2.setter
    def curse_2(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Curse_2 can only be set for relics")
        struct.pack_into("<I", self.data, 60, value)

    @property
    def curse_3(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 64)[0]

    @curse_3.setter
    def curse_3(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Curse_3 can only be set for relics")
        struct.pack_into("<I", self.data, 64, value)

    @property
    def unk_2(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return struct.unpack_from("<I", self.data, 68)[0]

    @unk_2.setter
    def unk_2(self, value):
        if self.type_bits != ITEM_TYPE_RELIC:
            raise TypeError("Unk_2 can only be set for relics")
        struct.pack_into("<I", self.data, 68, value)

    @property
    def effects_and_curses(self):
        if self.type_bits != ITEM_TYPE_RELIC:
            return None
        return [self.effect_1, self.effect_2, self.effect_3, self.curse_1, self.curse_2, self.curse_3]

    def __repr__(self):
        return f"ItemState(ga_handle=0x{self.ga_handle:08X}, item_id=0x{self.item_id:08X}, instance_id={self.instance_id}, real_item_id={self.real_item_id}, type_bits=0x{self.type_bits:08X}, size={self.size})"


class ItemEntry:
    # Item Entries Section Structure In user_data
    # First 4 bytes: Item count
    # Followed by ItemEntry structures (Base size 14 bytes):
    # - 4 bytes: ga_handle, Composite LE (Byte 0: Type 0xB0=Goods, 0xC0=Relics etc. Bytes 1-3: ID)
    # - 4 bytes: item_quantity, 0xB00003E9 -> GoodsId = 1001, Flask of Crimson Tears Default Quantity is 3
    # - 4 bytes: acquisition ID, Unique, this value does not repeat across all item entries.
    # - 1 byte: bool -> is favorite
    # - 1 byte: bool -> is new relic, if relic is marked as favorite or equipped by hero, this flag will be set false
    def __init__(self, data_bytes: bytearray):
        if len(data_bytes) != 14:
            raise ValueError("Invalid data length")
        self.ga_handle: int = struct.unpack_from("<I", data_bytes, 0)[0]  # Combination of ItemType and Instance ID
        self.type_bits = self.ga_handle & 0xF0000000
        self.instance_id = self.ga_handle & 0x00FFFFFF  # Tpye 'Goods' instance id is equal to goodsId
        self.item_amount = struct.unpack_from("<I", data_bytes, 4)[0]
        self.acquisition_id = struct.unpack_from("<I", data_bytes, 8)[0]
        self.is_favorite = bool(data_bytes[12])
        self.is_new = bool(data_bytes[13])
        self.state: ItemState = None
        self.equipped_by: list[int] = [0] * 10

    @classmethod
    def create_from_state(cls, state: ItemState, acquisition_id: int):
        entry = cls(bytearray(14))
        entry.ga_handle = state.ga_handle
        entry.instance_id = state.item_id
        entry.item_amount = 1
        entry.acquisition_id = acquisition_id
        entry.is_favorite = True
        entry.is_new = False
        return entry

    @property
    def data_bytes(self):
        _data = bytearray(14)
        struct.pack_into("<I", _data, 0, self.ga_handle)
        struct.pack_into("<I", _data, 4, self.item_amount)
        struct.pack_into("<I", _data, 8, self.acquisition_id)
        _data[12] = int(self.is_favorite)
        _data[13] = int(self.is_new)
        return _data

    @property
    def is_relic(self):
        return self.type_bits == ITEM_TYPE_RELIC

    @property
    def equipped_hero_types(self) -> list[int]:
        result = []
        for i in range(10):
            if self.equipped_by[i] > 0:
                result.append(i + 1)
        return result

    def link_state(self, state: ItemState):
        self.state = state

    def equip(self, hero_type: Literal[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]):
        self.equipped_by[hero_type-1] += 1
        self.is_new = False

    def unequip(self, hero_type: Literal[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]):
        self.equipped_by[hero_type-1] -= 1

    def mark_favorite(self):
        self.is_favorite = True
        self.is_new = False

    def mark_unfavorite(self):
        self.is_favorite = False

    def __repr__(self):
        return f"ItemEntry(ga_handle=0x{self.ga_handle:08X}, item_id={self.instance_id}, item_amount={self.item_amount}, acquisition_id={self.acquisition_id}, is_favorite={self.is_favorite}, is_new={self.is_new})"


class UnlockStateManager:
    """
    Placeholder class for game progress and unlock status.
        The specific data structure for this section is still under investigation.
        Established now for preliminary checks and to facilitate rapid implementation once
        the parsing logic is finalized.
    """
    def __init__(self):
        self.game_data = SourceDataHandler()

    def is_vessel_unlocked(self, vessel_id) -> bool:
        """
        Placeholder Checks if the vessel is unlocked based on game progress.
        Currently, all vessels are considered unlocked by default.

        :param vessel_id: The vessel ID to check.
        :type vessel_id: int
        :return: True if the vessel is unlocked, False otherwise.
        :rtype: bool
        """
        return True

    def is_character_unlocked(self, hero_type) -> bool:
        """
        Placeholder Checks if the character is unlocked based on game progress.
        Currently, all characters are considered unlocked by default.

        :param hero_type: The hero type ID to check.
        :type hero_type: int
        :return: True if the character is unlocked, False otherwise.
        :rtype: bool
        """
        return True


class InventoryHandler:
    _instance = None
    _lock = threading.RLock()
    _parse_lock = threading.Lock()
    _initialized = False

    START_OFFEST = 0x14  # Item State Datas start at offset 0x14
    STATE_SLOT_COUNT = 5120  # MAX slots count of Item States
    ENTRY_SLOT_COUNT = 3065  # MAX slots count of Item Entries
    STATE_SLOT_KEEP_COUNT = 84  # Item State slots are Empty from 0 to 83

    def __new__(cls):
        # Singleton Pattern
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super(InventoryHandler, cls).__new__(cls)
        return cls._instance

    def __init__(self):
        if self._initialized:
            return
        with self._lock:
            self.illegal_gas = []  # Track relic changes to prevent redundant full-set validity checks.
            self.curse_illegal_gas = []  # Track relics illegal due to missing curses
            self.strict_invalid_gas = []
            self.initialize()

    def initialize(self):
        """
        Initializes the InventoryHandler instance.
            This is called before the inventory parse.
            Excludes illegal_gas, curse_illegal_gas, and strict_invalid_gas.
            These should be initialized only once in __init__ or
            reset with set_illegal_relics.
        """
        self._initialized = True
        self.unlock_manager = UnlockStateManager()
        self.states: list[ItemState] = []
        self.entries: list[ItemEntry] = []
        self.relics: dict[int, ItemEntry] = {}
        self.relics_df: pd.DataFrame = None  # Load data only if required

        self.player_name_offset = 0
        self.entry_count_offset = 0
        self.entry_offset = 0
        self.murks_offset = 0
        self.sigs_offset = 0

        self.entry_count = 0
        self.vessels = [9600, 9603, 9606, 9609, 9612, 9615, 9618, 9621, 9900, 9910]  # Hero Default
        self.ga_to_acquisition_id = {}
        self._cur_last_instance_id = 0x800054  # start instance id
        self._cur_last_acquisition_id = 0
        self._free_state_indices: list[int] = []
        self._relic_min_index: int | None = None
        self._relic_max_index: int | None = None

        self.relic_gas = []

    @classmethod
    def get_player_name_from_data(cls, data):
        cur_offset = cls.START_OFFEST
        for i in range(cls.STATE_SLOT_COUNT):
            state = ItemState()
            state.from_bytes(data, cur_offset)
            cur_offset += state.size
        cur_offset += 0x94
        max_chars = 16
        for cur in range(cur_offset, cur_offset + max_chars * 2, 2):
            if data[cur:cur + 2] == b'\x00\x00':
                max_chars = (cur - cur_offset) // 2
                break
        raw_name = data[cur_offset:cur_offset + max_chars * 2]
        name = raw_name.decode("utf-16-le", errors="ignore").rstrip("\x00")
        return name if name else None

    def set_illegal_relics(self):
        checker = RelicChecker()
        illegal_relics = []
        curse_illegal_relics = []
        strict_invalid_relics = []
        relic_group_by_id: dict[int, list] = {}
        for ga in self.relic_gas:
            real_id = self.relics[ga].state.real_item_id
            if real_id not in relic_group_by_id.keys():
                relic_group_by_id[real_id] = []
            relic_group_by_id[real_id].append(ga)
            effects = self.relics[ga].state.effects_and_curses
            invalid_reason = checker.check_invalidity(real_id, effects)
            if invalid_reason != InvalidReason.NONE:
                illegal_relics.append(ga)
                # Check if it's specifically curse-illegal
                if is_curse_invalid(invalid_reason):
                    curse_illegal_relics.append(ga)
            elif checker.is_strict_invalid(real_id, effects, InvalidReason.NONE):
                # Valid but has effects with 0 weight in specific pool
                strict_invalid_relics.append(ga)

        for real_id, gas in relic_group_by_id.items():
            if real_id in UNIQUENESS_IDS:
                if len(gas) > 1:
                    legal_found = False
                    for ga in gas:
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
        logger.info(f"Update Illegal gas: 0x{ga_handle:08X}, {item_id}")
        checker = RelicChecker()
        invalid_reason = checker.check_invalidity(item_id, source_effects)
        if invalid_reason and ga_handle not in self.illegal_gas:
            self.append_illegal(ga_handle, is_curse_invalid(invalid_reason))
        elif not invalid_reason and ga_handle in self.illegal_gas:
            self.remove_illegal(ga_handle)
        if checker.is_strict_invalid(item_id, source_effects, invalid_reason):
            if ga_handle not in self.strict_invalid_gas:
                self.strict_invalid_gas.append(ga_handle)
        else:
            if ga_handle in self.strict_invalid_gas:
                self.strict_invalid_gas.remove(ga_handle)

    def request_new_instance_id(self):
        with self._lock:
            self._cur_last_instance_id += 1
            return self._cur_last_instance_id

    def request_new_acquisition_id(self):
        with self._lock:
            self._cur_last_acquisition_id += 1
            return self._cur_last_acquisition_id

    def parse(self):
        with self._lock:
            logger.info("Parsing inventory data")
            # Backup equipment state
            ga_to_equipped_by = {
                entry.ga_handle: entry.equipped_by.copy() for entry in self.entries
            }

            self.initialize()
            cur_offset = self.START_OFFEST
            state_ga_to_index = {}
            logger.info("Parsing inventory states. Starting at offset: 0x%X", cur_offset)
            for i in range(self.STATE_SLOT_COUNT):
                state = ItemState()
                state.from_bytes(globals.data, cur_offset)
                state.index = i
                self.states.append(state)
                if state.ga_handle != 0:
                    state_ga_to_index[state.ga_handle] = i
                self._cur_last_instance_id = max(self._cur_last_instance_id, state.instance_id)
                if state.ga_handle == 0 and i >= self.STATE_SLOT_KEEP_COUNT:
                    self._free_state_indices.append(i)
                if state.type_bits == ITEM_TYPE_RELIC and state.ga_handle != 0:
                    if self._relic_min_index is None:
                        self._relic_min_index = i
                    self._relic_max_index = i
                cur_offset += state.size

            cur_offset += 0x94
            self.player_name_offset = cur_offset
            self.murks_offset = cur_offset + 52
            self.sigs_offset = cur_offset - 64
            logger.info("Assuming player name offset at: 0x%X", cur_offset)
            cur_offset += 0x5B8
            self.entry_count_offset = cur_offset
            logger.info("Assuming entry count offset at: 0x%X", cur_offset)
            cur_offset += 0x4
            self.entry_offset = cur_offset
            logger.info("Assuming entry offset at: 0x%X", cur_offset)

            logger.info("Parsing inventory entries. Starting at offset: 0x%X", cur_offset)
            for i in range(self.ENTRY_SLOT_COUNT):
                entry = ItemEntry(globals.data[cur_offset:cur_offset+14])
                self.entries.append(entry)
                if entry.instance_id in range(9600, 9957):
                    self.vessels.append(entry.instance_id)
                cur_offset += 14
                if entry.ga_handle != 0:
                    self.entry_count += 1
                self._cur_last_acquisition_id = max(self._cur_last_acquisition_id, entry.acquisition_id)
                if entry.is_relic:
                    entry.link_state(self.states[state_ga_to_index[entry.ga_handle]])
                    self.ga_to_acquisition_id[entry.ga_handle] = entry.acquisition_id
                    self.relics[entry.ga_handle] = entry
                    self.relic_gas.append(entry.ga_handle)
                    # Restore equipment state
                    entry.equipped_by = ga_to_equipped_by.get(entry.ga_handle, [])

            count_in_data = struct.unpack_from("<I", globals.data, self.entry_count_offset)[0]
            if self.entry_count != count_in_data:
                logger.warning("Entry count mismatch: counted %d, data has %d", self.entry_count, count_in_data)
                logger.warning("Trying to fix it...")
                logger.info("Updating entry count in")
                struct.pack_into("<I", globals.data, self.entry_count_offset, self.entry_count)

    def update_entry_data(self, entry_index: int, parse_after_update=True):
        target_offset = self.entry_offset + entry_index * 14
        globals.data = globals.data[:target_offset] + self.entries[entry_index].data_bytes + globals.data[target_offset + 14:]
        if parse_after_update:
            self.parse()

    def _pop_free_slot_for_relic(self) -> int:
        """Select and remove the best free state slot for a new relic.

        Priority order:
          1. Any free slot inside the relic cluster [min, max] — fill gaps first.
          2. The nearest free slot to the left of relic_min — extend left.
          3. The nearest free slot to the right of relic_max — extend right.
          4. Fallback: the first free slot (smallest index).
        """
        free = self._free_state_indices
        if not free:
            raise RuntimeError("No empty slot found in inventory states to add relic.")

        relic_min = self._relic_min_index
        relic_max = self._relic_max_index

        if relic_min is None or relic_max is None:
            # No relics exist yet — take the smallest free index
            return free.pop(0)

        # Priority 1: any free slot inside the relic cluster
        for i in free:
            if relic_min <= i <= relic_max:
                free.remove(i)
                return i

        # Priority 2: nearest free slot to the left of relic_min
        left_candidates = [i for i in free if i < relic_min]
        if left_candidates:
            i = max(left_candidates)
            free.remove(i)
            return i

        # Priority 3: nearest free slot to the right of relic_max
        right_candidates = [i for i in free if i > relic_max]
        if right_candidates:
            i = min(right_candidates)
            free.remove(i)
            return i

        # Priority 4: fallback — smallest free index
        return free.pop(0)

    def add_relic_to_inventory(self, relic_type: str = "normal"):
        with self._lock:
            logger.info("Adding relic to inventory")
            # Create dummy relic state first
            dummy_relic = ItemState.create_dummy_relic(self.request_new_instance_id(),
                                                       relic_type=relic_type)
            # Replace Item Entry at empty slot
            empty_entry_index = -1
            for i in range(self.ENTRY_SLOT_COUNT):
                entry = self.entries[i]
                if entry.ga_handle == 0:
                    # Found an empty slot
                    empty_entry_index = i
                    break
            else:
                raise RuntimeError("No empty slot found in inventory entries to add relic.")

            # Pop an empty state slot with optimal locality for relics
            empty_state_index = self._pop_free_slot_for_relic()

            # Replace Item Entry
            self.entries[empty_entry_index] = ItemEntry.create_from_state(dummy_relic, self.request_new_acquisition_id())
            _new_enty_data = self.entries[empty_entry_index].data_bytes
            # Replace entry data
            target_offset = self.entry_offset + empty_entry_index * 14
            logger.info("Adding relic at offset: 0x%X", target_offset)
            globals.data = globals.data[:self.entry_offset+empty_entry_index*14] + _new_enty_data + globals.data[self.entry_offset+(empty_entry_index+1)*14:]
            # Update entry count
            self.entry_count += 1
            struct.pack_into("<I", globals.data, self.entry_count_offset, self.entry_count)
            logger.info("Added relic at entry index %d", empty_entry_index)

            # Replace Item State data
            old_size = self.states[empty_state_index].size
            dummy_relic.index = empty_state_index
            self.states[empty_state_index] = dummy_relic
            _new_state_data = self.states[empty_state_index].data
            _cur_offset = self.START_OFFEST + sum(state.size for state in self.states[:empty_state_index])
            globals.data = globals.data[:_cur_offset] + _new_state_data + globals.data[_cur_offset + old_size:]
            remove_padding_area()
            logger.info("Added relic at state index %d", empty_state_index)
            logger.info(f"New Relic State Info:{repr(dummy_relic)}")
            logger.info(f"New Relic Entry Info:{repr(self.entries[empty_entry_index])}")
            self.parse()  # Just make sure everything is fine
            return True, self.entries[empty_entry_index].ga_handle

    def remove_relic_from_inventory(self, ga_handle):
        if self.get_relic_equipped_by(ga_handle):
            raise ValueError("Cannot remove an equipped relic")

        with self._lock:
            logger.info("Removing relic from inventory")
            target_state_index = -1
            for i in range(self.STATE_SLOT_COUNT):
                if self.states[i].ga_handle == ga_handle:
                    target_state_index = i
                    logger.info("Found relic at state index %d", target_state_index)
                    break
            else:
                raise ValueError("Relic not found in inventory")
            target_entry_index = -1
            for i in range(self.ENTRY_SLOT_COUNT):
                if self.entries[i].ga_handle == ga_handle:
                    target_entry_index = i
                    logger.info("Found relic at entry index %d", target_entry_index)
                    break
            else:
                raise ValueError("Relic not found in inventory")

            # Replace target entry by 0
            logger.info("Removing relic at entry index %d", target_entry_index)
            self.entries[target_entry_index] = ItemEntry(bytearray(14))
            _new_enty_data = self.entries[target_entry_index].data_bytes
            globals.data = globals.data[:self.entry_offset+target_entry_index*14] + _new_enty_data + globals.data[self.entry_offset+(target_entry_index+1)*14:]
            # Update entry count
            logger.info(f"Updating entry count in inventory from {self.entry_count} to {self.entry_count - 1}")
            self.entry_count -= 1
            struct.pack_into("<I", globals.data, self.entry_count_offset, self.entry_count)
            logger.info("Removed relic at entry index %d", target_entry_index)

            # Replace target state by 0
            logger.info("Removing relic at state index %d", target_state_index)
            old_size = self.states[target_state_index].size
            self.states[target_state_index] = ItemState()
            _new_state_data = self.states[target_state_index].data
            _cur_offset = self.START_OFFEST + sum(state.size for state in self.states[:target_state_index])
            globals.data = globals.data[:_cur_offset] + _new_state_data + globals.data[_cur_offset + old_size:]
            logger.info("Fill padding area with 0x00")
            insert_padding_area()
            logger.info("Removed relic at state index %d", target_state_index)
            if target_state_index >= self.STATE_SLOT_KEEP_COUNT:
                self._free_state_indices.append(target_state_index)
            self.parse()  # Just make sure everything is fine
            self.remove_illegal(ga_handle)
            return True

    def update_relic_state(self, state_index):
        with self._lock:
            logger.info("Updating relic state")
            # Only relics can have their state updated
            if self.states[state_index].type_bits != globals.ITEM_TYPE_RELIC:
                raise TypeError("Only relics can have their state updated")

            # Assume item type wasn't change
            target_offset = self.START_OFFEST + sum(state.size for state in self.states[:state_index])
            globals.data = globals.data[:target_offset] + self.states[state_index].data + globals.data[target_offset + self.states[state_index].size:]
            self.parse()  # Just make sure everything is fine

    def modify_relic(self, ga_handle, relic_id=None,
                     effect_1=None, effect_2=None, effect_3=None,
                     curse_1=None, curse_2=None, curse_3=None):
        with self._lock:
            type_bits = ga_handle & 0xF0000000
            if type_bits != globals.ITEM_TYPE_RELIC:
                raise TypeError("Only relics can be modified")

            logger.info("Modifying relic in inventory")
            target_state_index = self.relics[ga_handle].state.index

            if relic_id is not None:
                self.states[target_state_index].set_real_id(relic_id)
            if effect_1 is not None:
                self.states[target_state_index].effect_1 = effect_1
            if effect_2 is not None:
                self.states[target_state_index].effect_2 = effect_2
            if effect_3 is not None:
                self.states[target_state_index].effect_3 = effect_3
            if curse_1 is not None:
                self.states[target_state_index].curse_1 = curse_1
            if curse_2 is not None:
                self.states[target_state_index].curse_2 = curse_2
            if curse_3 is not None:
                self.states[target_state_index].curse_3 = curse_3

            # for i in range(self.STATE_SLOT_KEEP_COUNT, self.STATE_SLOT_COUNT):
            #     if self.states[i].ga_handle == ga_handle:
            #         target_state_index = i
            #         if relic_id is not None:
            #             self.states[target_state_index].set_real_id(relic_id)
            #         if effect_1 is not None:
            #             self.states[target_state_index].effect_1 = effect_1
            #         if effect_2 is not None:
            #             self.states[target_state_index].effect_2 = effect_2
            #         if effect_3 is not None:
            #             self.states[target_state_index].effect_3 = effect_3
            #         if curse_1 is not None:
            #             self.states[target_state_index].curse_1 = curse_1
            #         if curse_2 is not None:
            #             self.states[target_state_index].curse_2 = curse_2
            #         if curse_3 is not None:
            #             self.states[target_state_index].curse_3 = curse_3
            #         break
            # else:
            #     raise ValueError("Relic not found in inventory")
            self.update_relic_state(target_state_index)
            self.update_illegal(ga_handle,
                                self.states[target_state_index].real_item_id,
                                self.states[target_state_index].effects_and_curses)
            return True

    @property
    def murks(self):
        return int(struct.unpack_from("<I", globals.data, self.murks_offset)[0])

    @murks.setter
    def murks(self, value):
        struct.pack_into("<I", globals.data, self.murks_offset, value)

    @property
    def sigs(self):
        return int(struct.unpack_from("<I", globals.data, self.sigs_offset)[0])

    @sigs.setter
    def sigs(self, value):
        struct.pack_into("<I", globals.data, self.sigs_offset, value)

    def reset_equipped_records(self):
        for entry in self.entries:
            entry.equipped_by = [0] * 10

    def get_relic_equipped_by(self, ga_handle):
        try:
            return self.relics[ga_handle].equipped_hero_types
        except KeyError:
            return []

    def equip_relic(self, ga_handle, hero_type):
        try:
            # Record flag changes to determine whether to update entry data.
            old_new_flag = self.relics[ga_handle].is_new
            self.relics[ga_handle].equip(hero_type)
            new_new_flag = self.relics[ga_handle].is_new
            if old_new_flag == new_new_flag:
                # If is_new flag didn't change, no need to update
                return
            for idx, entry in enumerate(self.entries):
                if entry.ga_handle == ga_handle:
                    self.update_entry_data(idx)
        except KeyError:
            raise ValueError("Relic not found in inventory")

    def unequip_relic(self, ga_handle, hero_type):
        try:
            self.relics[ga_handle].unequip(hero_type)
        except KeyError:
            raise ValueError("Relic not found in inventory")

    def toggle_favorite_mark(self, ga_handle):
        try:
            cur_favorite = self.relics[ga_handle].is_favorite
            if cur_favorite:
                self.relics[ga_handle].mark_unfavorite()
            else:
                self.relics[ga_handle].mark_favorite()
            for idx, entry in enumerate(self.entries):
                if entry.ga_handle == ga_handle:
                    self.update_entry_data(idx, False)
            return self.relics[ga_handle].is_favorite
        except KeyError:
            raise ValueError("Relic not found in inventory")

    def stringify_relic_effects(self, ga_handles: list[int]):
        output = ""
        for ga_handle in ga_handles:
            relic = self.relics[ga_handle].state
            effects = [
                -1 if eff in (0, 0xFFFFFFFF) else eff
                for eff in relic.effects_and_curses
            ]
            output += " | ".join(str(eff) for eff in effects) + "\n"
        return output.strip()

    def parse_effects(self, effects_string: str) -> list[list[int]]:
        result = []
        lines = effects_string.strip().split("\n")
        for n, line in enumerate(lines):
            line = line.strip()
            if not line:
                continue
            effects = [
                0xFFFFFFFF if int(eff) == -1 else int(eff) for eff in line.split("|")
            ]
            if len(effects) != 6:
                raise ValueError(f"Not enough effects (line: {n+1})")
            result.append(effects)
        return result

    def reindex_acquisition_id_at(self, start_acquisition_id: int, *ga_handles: int):
        """
        Reindexes acquisition IDs starting from a specific value for the given handles.

        This method assigns sequential IDs to entries matching ga_handles starting at
        start_acquisition_id. To prevent ID collisions, any existing entries with an
        ID greater than or equal to the start value are shifted forward.

        Args:
            start_acquisition_id: The base ID to start assigning from.
            *ga_handles: The target handles to be repositioned or updated.
        """
        for i, entry in enumerate(self.entries):
            if entry.ga_handle in ga_handles:
                entry.acquisition_id = start_acquisition_id + ga_handles.index(
                    entry.ga_handle
                )
                self.update_entry_data(i, False)
            elif entry.acquisition_id >= start_acquisition_id:
                entry.acquisition_id += len(ga_handles)
                self.update_entry_data(i, False)
        # self.parse will calculate new last acquisition id
        # so we don't need to update it here
        # self._cur_last_acquisition_id += len(ga_handles)
        self.parse()

    def refresh_relics_dataframe(self):
        cols = ['ga_handle', 'relic_id', 'effect_1', 'effect_2', 'effect_3',
                'curse_1', 'curse_2', 'curse_3']

        rows = []
        for ga_handle, entry in self.relics.items():
            relic_id = entry.state.real_item_id
            effects = entry.state.effects_and_curses

            row = [ga_handle, relic_id] + effects
            rows.append(row)

        self.relics_df = pd.DataFrame(rows, columns=cols)

    def debug_print(self, non_zero_only=False):
        for i, state in enumerate(self.states):
            if state.ga_handle == 0 and non_zero_only:
                continue
            logger.debug(f"State {i}: {state}")
        for i, entry in enumerate(self.entries):
            if entry.ga_handle == 0 and non_zero_only:
                continue
            logger.debug(f"Entry {i}: {entry}")
        logger.debug(f"Player Name Offset: {self.player_name_offset}")
        logger.debug(f"Entry Offset: {self.entry_count_offset}")
        logger.debug(f"Entry Count: {self.entry_count}")
        logger.debug(f"Vessels: {self.vessels}")
        logger.debug(f"Last Instance ID: {self._cur_last_instance_id}")
        logger.debug(f"Last Acquisition ID: {self._cur_last_acquisition_id}")

    def debug_relic_print(self):
        game_data = SourceDataHandler()  # Singleton
        for ga_handle, entry in self.relics.items():
            relic_id = entry.state.real_item_id
            relic_name = game_data.relics[relic_id].name
            relic_effects = entry.state.effects_and_curses
            relic_effects_names = [game_data.effects[effect].name for effect in relic_effects]
            logger.debug(f"Relic GA: 0x{ga_handle:X}, ID: {relic_id}, Name: {relic_name}, Effects/Curses: {relic_effects_names}")

    def debug_entry_print(self):
        for entry in self.relics.values():
            logger.debug(f"Entry: {repr(entry)}")
