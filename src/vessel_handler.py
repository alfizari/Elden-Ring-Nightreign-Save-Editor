import datetime
import os
import struct
import re
from copy import deepcopy
import orjson
import logging
from source_data_handler import SourceDataHandler
from relic_checker import RelicChecker
from inventory_handler import InventoryHandler, ItemEntry
import globals
from globals import ITEM_TYPE_RELIC, COLOR_MAP, get_now_timestamp, UNIQUENESS_IDS


logger = logging.getLogger(__name__)


def is_vessel_available(vessel_id: int):
    try:
        game_data = SourceDataHandler()  # SourceDataHandler is a singleton Class
        inventory = InventoryHandler()  # InventoryHandler is a singleton Class
        _vessel_goods_id = game_data.vessels[vessel_id].goods_id
        return _vessel_goods_id in inventory.vessels and inventory.unlock_manager.is_vessel_unlocked(vessel_id)
    except KeyError:
        return False


class HeroLoadout:
    def __init__(self, hero_type, cur_preset_idx, cur_vessel_id, vessels, offsets):
        self.hero_type = hero_type
        self.cur_preset_idx = cur_preset_idx
        self.cur_vessel_id = cur_vessel_id
        # vessel list[dict]， keys: vessel_id, relics, offsets:dict
        #   offsets store offests for vessel_id and relics, keys: vessel_id, relics
        self.vessels = vessels
        self.presets = []
        # Stores offsets for hero-level fields
        self.offsets = offsets

    def add_preset(self, hero_type, index, name, vessel_id, relics, offsets, counter, timestamp):
        inventory = InventoryHandler()  # InventoryHandler is a singleton Class
        self.presets.append({
            "hero_type": hero_type,
            "index": index,
            "name": name,
            "vessel_id": vessel_id,
            "relics": relics,
            "offsets": offsets,
            "counter": counter,
            "timestamp": timestamp
        })
        for r in relics:
            if (r & 0xF0000000) == ITEM_TYPE_RELIC and r != 0:
                inventory.equip_relic(r, hero_type)

    def auto_adjust_cur_equipment(self):
        """
        Automatically adjust the current preset index based on the current vessel's relics.
        """
        _new_preset_idx = 0xFF
        _vessel_idx = 0
        for idx, v in enumerate(self.vessels):
            if v["vessel_id"] == self.cur_vessel_id:
                _vessel_idx = idx
                break

        for preset in self.presets:
            if preset["vessel_id"] == self.cur_vessel_id and preset['relics'] == self.vessels[_vessel_idx]["relics"]:
                _new_preset_idx = preset["index"]
                break
        self.cur_preset_idx = _new_preset_idx

    def get_export_data(self):
        """
        Retrieves and formats the current hero loadout for export.

        This function processes the internal hero data and converts it into a
        structured 'HeroLoadout' format suitable for storage.

        Note:
            The output data structure differs slightly from the import
            format to ensure compatibility with storage requirements.

        Returns:
            dict: A dictionary representing the HeroLoadout structure,
                optimized for saving.
        """
        inventory = InventoryHandler()  # InventoryHandler is a singleton Class
        _vessels = []
        _presets = []
        _all_needed_relics = []
        _all_needed_relics_ga = set()
        for v in self.vessels:
            _relics = []
            for r in v["relics"]:
                if r != 0 and (r & 0xF0000000) == ITEM_TYPE_RELIC:
                    _relic = {
                        "relic_id": inventory.relics[r].state.real_item_id,
                        "effect_1": inventory.relics[r].state.effect_1,
                        "effect_2": inventory.relics[r].state.effect_2,
                        "effect_3": inventory.relics[r].state.effect_3,
                        "curse_1": inventory.relics[r].state.curse_1,
                        "curse_2": inventory.relics[r].state.curse_2,
                        "curse_3": inventory.relics[r].state.curse_3
                        }
                    if r not in _all_needed_relics_ga:
                        _all_needed_relics_ga.add(r)
                        _all_needed_relics.append(_relic)
                    _relics.append(_relic)
                else:
                    _relics.append({
                        "relic_id": 0,
                        "effect_1": 0xffffffff,
                        "effect_2": 0xffffffff,
                        "effect_3": 0xffffffff,
                        "curse_1": 0xffffffff,
                        "curse_2": 0xffffffff,
                        "curse_3": 0xffffffff
                    })
            _vessels.append({
                "vessel_id": v["vessel_id"],
                "relics": _relics
            })

        for p in self.presets:
            _relics = []
            for r in p["relics"]:
                if r != 0 and (r & 0xF0000000) == ITEM_TYPE_RELIC:
                    _relic = {
                        "relic_id": inventory.relics[r].state.real_item_id,
                        "effect_1": inventory.relics[r].state.effect_1,
                        "effect_2": inventory.relics[r].state.effect_2,
                        "effect_3": inventory.relics[r].state.effect_3,
                        "curse_1": inventory.relics[r].state.curse_1,
                        "curse_2": inventory.relics[r].state.curse_2,
                        "curse_3": inventory.relics[r].state.curse_3
                        }
                    if r not in _all_needed_relics_ga:
                        _all_needed_relics_ga.add(r)
                        _all_needed_relics.append(_relic)
                    _relics.append(_relic)
                else:
                    _relics.append({
                        "relic_id": 0,
                        "effect_1": 0xffffffff,
                        "effect_2": 0xffffffff,
                        "effect_3": 0xffffffff,
                        "curse_1": 0xffffffff,
                        "curse_2": 0xffffffff,
                        "curse_3": 0xffffffff
                    })
            _presets.append({
                "name": p["name"],
                "vessel_id": p["vessel_id"],
                "relics": _relics
            })

        export_dict = {
            "hero_type": self.hero_type,
            "cur_vessel_id": self.cur_vessel_id,
            "vessels": _vessels,
            "presets": _presets,
            "all_needed_relics": _all_needed_relics
        }
        return export_dict

    def import_vessels(self, im_vessels: list, vessel_indices: list[int]):
        """
        Imports and restores vessel relic configurations from exported data.

        This method MUST be executed after presets are imported to ensure
        `auto_adjust_cur_equipment` can correctly synchronize the state.

        Unlike the export process, the imported relic information must be
        processed through the `InventoryHandler`. It performs a lookup to map
        relic metadata back to their unique 'ga_handle' (int), which forms
        the ordered list within each vessel.

        Args:
            im_vessels (list): A list of vessel dictionaries containing relic
                info retrieved from an exported file (generated by `get_export_data`).

            vessel_indices (list): A list of indices specifying which vessels should be imported.

        Note:
            The mapping logic relies on the `InventoryHandler` to resolve the
            relationship between serialized relic data and active 'ga_handle' IDs.
        """
        inventory = InventoryHandler()  # InventoryHandler is a singleton Class
        game_data = SourceDataHandler()  # SourceDataHandler is a singleton Class
        result_msgs = []
        for idx, im_v in enumerate(im_vessels):
            if idx not in vessel_indices:
                result_msgs.append(f"{game_data.vessels[im_v['vessel_id']].name} skipped.")
                continue
            for v in self.vessels:
                if v["vessel_id"] == im_v["vessel_id"]:
                    if not is_vessel_available(v["vessel_id"]):
                        result_msgs.append(f"{game_data.vessels[v['vessel_id']].name} import failed. Vessel is not unlocked.")
                        break
                    for r in v["relics"]:
                        if r != 0:
                            inventory.unequip_relic(r, self.hero_type)
                    v["relics"] = im_v["relics"]
                    for r in v["relics"]:
                        if r != 0:
                            inventory.equip_relic(r, self.hero_type)
                    result_msgs.append(f"{game_data.vessels[v['vessel_id']].name} imported successfully.")
                    break
            else:
                result_msgs.append(f"Vessel {im_v['vessel_id']} not found in hero loadout.")
        self.auto_adjust_cur_equipment()
        return result_msgs


class VesselParser:
    # Items type
    ITEM_TYPE_EMPTY = 0x00000000
    ITEM_TYPE_WEAPON = 0x80000000
    ITEM_TYPE_ARMOR = 0x90000000
    ITEM_TYPE_RELIC = 0xC0000000

    def __init__(self):
        self.game_data = SourceDataHandler()  # Singleton
        self.inventory = InventoryHandler()  # Singleton
        self.heroes: dict[int, HeroLoadout] = {}
        self.relic_ga_hero_map = {}
        self.base_offset = None

    def parse(self):
        heroes = {}
        self.relic_ga_hero_map = {}
        self.inventory.reset_equipped_records()
        self.base_offset = None
        magic_pattern = re.escape(bytes.fromhex("C2000300002C000003000A0004004600"))
        marker = re.escape(bytes.fromhex("64000000"))

        match = re.search(magic_pattern + marker, globals.data)
        if not match:
            print("[Error] Magic pattern not found.")
            return

        cursor = match.start()

        # Record the start of the entire block if needed
        cursor = match.end()
        self.base_offset = cursor

        # 1. Hero ID Section (Fixed 10 heroes)
        last_hero_type = None
        for _ in range(10):
            # Record hero-level offsets
            h_start = cursor
            hero_type, cur_idx = struct.unpack_from("<BB", globals.data, cursor)
            hero_type = int(hero_type)
            cur_idx = int(cur_idx)

            hero_offsets = {
                "base": h_start,
                "cur_preset_idx": h_start + 1,
                "cur_vessel_id": h_start + 4
            }
            cursor += 4  # Skip ID, Idx, Padding

            cur_v_id = struct.unpack_from("<I", globals.data, cursor)[0]
            cursor += 4

            universal_vessels = []
            for _ in range(4):
                v_start = cursor
                v_id = struct.unpack_from("<I", globals.data, cursor)[0]
                cursor += 4
                relics = list(struct.unpack_from("<6I", globals.data, cursor))
                for r in relics:
                    if (r & 0xF0000000) == self.ITEM_TYPE_RELIC and r != 0:
                        if r not in self.relic_ga_hero_map:
                            self.relic_ga_hero_map[r] = set()
                        self.relic_ga_hero_map[r].add(hero_type)
                        self.inventory.equip_relic(r, hero_type)
                universal_vessels.append({
                    "vessel_id": v_id,
                    "relics": relics,
                    "offsets": {
                        "vessel_id": v_start,
                        "relics": v_start + 4
                    }
                })
                cursor += 24

            heroes[hero_type] = HeroLoadout(hero_type, cur_idx, cur_v_id, universal_vessels, hero_offsets)
            last_hero_type = hero_type

        # 2. Hero Vessels
        while cursor < len(globals.data):
            v_start = cursor
            v_id = struct.unpack_from("<I", globals.data, cursor)[0]
            if v_id == 0:
                cursor += 4
                break

            cursor += 4
            relics = list(struct.unpack_from("<6I", globals.data, cursor))

            v_meta = self.game_data.vessels.get(v_id)
            target_hero = v_meta.hero_type if v_meta else None
            assigned_id = last_hero_type if target_hero == 11 else target_hero

            for r in relics:
                if (r & 0xF0000000) == self.ITEM_TYPE_RELIC and r != 0:
                    if r not in self.relic_ga_hero_map:
                        self.relic_ga_hero_map[r] = set()
                    self.relic_ga_hero_map[r].add(assigned_id)
                    self.inventory.equip_relic(r, assigned_id)

            if assigned_id in heroes:
                heroes[assigned_id].vessels.append({
                    "vessel_id": v_id,
                    "relics": relics,
                    "offsets": {
                        "vessel_id": v_start,
                        "relics": v_start + 4
                    }
                })
            cursor += 24
        # Sort hero loadout vessels by vessel id
        for h_type in heroes:
            heroes[h_type].vessels.sort(key=lambda x: x["vessel_id"])

        # 3. Custom Presets Section
        preset_index = 0
        while cursor < len(globals.data):
            p_start = cursor
            header = struct.unpack_from("<B", globals.data, cursor)[0]
            if header != 0x01:
                break

            # Offsets for custom preset fields
            p_offsets = {
                "base": p_start,
                "hero_type": p_start + 1,
                "counter": p_start + 3,
                "name": p_start + 4,
                "vessel_id": p_start + 44,  # 4 + 36 + 4 padding
                "relics": p_start + 48,
                "timestamp": p_start + 72  # not sure
            }

            cursor += 1
            h_id = int(struct.unpack_from("<H", globals.data, cursor)[0])
            cursor += 2
            counter_val = struct.unpack_from("<B", globals.data, cursor)[0]
            cursor += 1

            name = globals.data[cursor:cursor + 36].decode('utf-16', errors='ignore').strip('\x00')
            cursor += 36 + 4  # Name + Padding

            v_id = struct.unpack_from("<I", globals.data, cursor)[0]
            cursor += 4

            relics = list(struct.unpack_from("<6I", globals.data, cursor))
            cursor += 24  # Relics
            for r in relics:
                if (r & 0xF0000000) == self.ITEM_TYPE_RELIC and r != 0:
                    if r not in self.relic_ga_hero_map:
                        self.relic_ga_hero_map[r] = set()
                    self.relic_ga_hero_map[r].add(h_id)
                    self.inventory.equip_relic(r, h_id)

            timestamp = struct.unpack_from("<Q", globals.data, cursor)[0]  # not sure
            cursor += 8

            if h_id in heroes:
                heroes[h_id].add_preset(h_id, preset_index, name, v_id, relics, p_offsets, counter_val, timestamp)

            preset_index += 1

            if counter_val == 0:
                break
        self.heroes = heroes

    def display_results(self):
        """
        Terminal output with formatted offsets (06X), hero_type (int), and relics (08X).
        """
        print(f"\n{'='*80}")
        print(f"{'Vessel Parser Results':^80}")
        print(f"{'='*80}")

        # Sort by hero_type for a cleaner list
        for h_id in sorted(self.heroes.keys()):
            loadout = self.heroes[h_id]
            h_off = loadout.offsets

            print(f"\n[Hero ID: {h_id}]")
            print(f"  - Base Offset: 0x{h_off['base']:06X}")
            print(f"  - Current Preset Index: {loadout.cur_preset_idx if loadout.cur_preset_idx != 255 else 'None'} (At: 0x{h_off['cur_preset_idx']:06X})")
            print(f"  - Current Vessel ID: {loadout.cur_vessel_id} (At: 0x{h_off['cur_vessel_id']:06X})")

            # Vessels Section
            print(f"  - Vessels ({len(loadout.vessels)} total):")
            for i, v in enumerate(loadout.vessels):
                v_off = v['offsets']
                relics_str = ", ".join([f"0x{r:08X}" for r in v['relics']])
                print(f"    [{i:02d}] ID: {v['vessel_id']} (At: 0x{v_off['vessel_id']:06X})")
                print(f"         Relics: [{relics_str}] (At: 0x{v_off['relics']:06X})")

            # Custom Presets Section
            if loadout.presets:
                print(f"  - Custom Presets ({len(loadout.presets)} total):")
                for p in loadout.presets:
                    p_off = p['offsets']
                    relics_str = ", ".join([f"0x{r:08X}" for r in p['relics']])
                    print(f"    * Name: {p['name']:<18} (At: 0x{p_off['name']:06X})")
                    print(f"      Index: {p['index']:<2}")
                    print(f"      Counter: {p.get('counter', 'N/A'):>2}      (At: 0x{p_off['counter']:06X})")
                    print(f"      Vessel ID: {p['vessel_id']:<8} (At: 0x{p_off['vessel_id']:06X})")
                    print(f"      Relics: [{relics_str}] (At: 0x{p_off['relics']:06X})")
                    print(f"      Timestamp: {p.get('timestamp', 'N/A')} (At: 0x{p_off['timestamp']:06X})")
            else:
                print("  - No Custom Presets found.")

        # print ga_hero_type_map
        print(f"\n{'='*80}")
        print(f"{'Relic GA Handle to Hero Type Map':^80}")
        print(f"{'='*80}")
        for r_ga in sorted(self.relic_ga_hero_map.keys()):
            heroes = self.relic_ga_hero_map[r_ga]
            heroes_str = ", ".join([str(h) for h in heroes])
            print(f"0x{r_ga:08X}: [{heroes_str}]")

        print(f"\n{'='*80}")


class VesselModifier:
    def __init__(self):
        """
        Initialize the modifier with binary data.
        :param data: The original binary data from the save file.
        """
        pass

    def update_hero_loadout(self, hero_loadout: HeroLoadout):
        """
        Update all fields of a specific hero loadout based on its offsets.
        """
        # 1. Update Hero-level fields
        struct.pack_into("<B", globals.data, hero_loadout.offsets["cur_preset_idx"], hero_loadout.cur_preset_idx)
        struct.pack_into("<I", globals.data, hero_loadout.offsets["cur_vessel_id"], hero_loadout.cur_vessel_id)

        # 2. Update Vessels (including Global sequences assigned to this hero)
        for v in hero_loadout.vessels:
            struct.pack_into("<I", globals.data, v["offsets"]["vessel_id"], v["vessel_id"])
            struct.pack_into("<6I", globals.data, v["offsets"]["relics"], *v["relics"])

        # 3. Update Custom Presets
        for p in hero_loadout.presets:
            p_off = p["offsets"]
            # Make sure header is 0x01 and hero_type is correct
            struct.pack_into("<B", globals.data, p_off["base"], 0x01)
            struct.pack_into("<H", globals.data, p_off["hero_type"], p["hero_type"])
            # Update counter
            struct.pack_into("<B", globals.data, p_off["counter"], p["counter"])

            # Update Vessel ID and Relics in preset
            struct.pack_into("<I", globals.data, p_off["vessel_id"], p["vessel_id"])
            struct.pack_into("<6I", globals.data, p_off["relics"], *p["relics"])

            # Update Name (if modified, ensuring it's 36 bytes UTF-16)
            name_bytes = p["name"].encode('utf-16le').ljust(36, b'\x00')[:36]
            globals.data[p_off["name"]:p_off["name"] + 36] = name_bytes

            # Update Timestamp
            struct.pack_into("<Q", globals.data, p_off["timestamp"], p["timestamp"])

    def update_all_loadouts(self, heroes: dict):
        """
        Update all hero loadouts.
        """
        for hero_loadout in heroes.values():
            self.update_hero_loadout(hero_loadout)

    def set_value(self, offset: int, fmt: str, value):
        """
        Generic method to set a value at a specific offset.
        :param fmt: struct format string (e.g., '<I', '<B')
        """
        struct.pack_into(fmt, globals.data, offset, value)


class Validator:
    def __init__(self):
        self.game_data = SourceDataHandler()  # Singleton
        self.inventory = InventoryHandler()  # Singleton

    def check_hero(self, heroes: dict[int, HeroLoadout], hero_type: int):
        if not 1 <= hero_type <= 10:
            raise ValueError("Invalid hero type")
        if hero_type not in heroes:
            raise BufferError("Hero not found. The Hero Loadout Structure may be corrupted.")
        return True

    def check_vessel_assignment(self, heroes: dict[int, HeroLoadout], hero_type: int, vessel_id: int):
        if self.check_hero(heroes, hero_type):
            _vessel_info = self.game_data.vessels.get(vessel_id)
            if not _vessel_info:
                raise ImportError("Can't find vessel data.")

            if _vessel_info.hero_type != 11 and _vessel_info.hero_type != hero_type:
                raise ValueError("This vessel is not assigned to this hero")
            else:
                if vessel_id not in [v["vessel_id"] for v in heroes[hero_type].vessels]:
                    raise BufferError("Vessel should be assigned to this hero but not found. The Hero Loadout Structure may be corrupted.")

            return True
        return False

    def validate_vessel(self, heroes: dict[int, HeroLoadout], hero_type: int, vessel:dict):
        # Check is vessel assigned to correct hero
        if self.check_vessel_assignment(heroes, hero_type, vessel["vessel_id"]):
            _vessel_info = self.game_data.vessels[vessel["vessel_id"]]
            # Check whether the relic in each relic slot is valid.
            for relic_index, relic in enumerate(vessel["relics"]):
                if relic == 0:
                    # Empty always Valid
                    continue
                relic_entry: ItemEntry = self.inventory.relics.get(relic)
                if not relic_entry:
                    # Can't find relic in inventory
                    raise LookupError("Relic not found in current relics Inventory.")
                if relic_entry.is_relic:
                    real_id = relic_entry.state.real_item_id
                    # Check relic type match
                    is_deep_relic = RelicChecker.is_deep_relic(real_id)
                    if relic_index < 3 and is_deep_relic:
                        # relic type mismatch
                        raise ValueError(f"Found deep slot with normal relic. Slot:{relic_index+1}")
                    if relic_index >= 3 and not is_deep_relic:
                        # relic type mismatch
                        raise ValueError(f"Found normal slot with deep relic. Slot:{relic_index+1}")
                    # Check color match
                    slot_color = COLOR_MAP[_vessel_info.relic_slots[relic_index]]
                    new_relic_color = self.game_data.relics[real_id].color
                    if slot_color != new_relic_color and slot_color != COLOR_MAP[4]:
                        # Color mismatch
                        raise ValueError(f"Color mismatch in relic slot {relic_index+1}.")
                    # Check duplicate relics in vessel
                    if 0 <= relic_index < 2:
                        for idx, relic_after in enumerate(vessel["relics"][relic_index + 1:3]):
                            r_af_idx = relic_index + 1 + idx
                            if relic_after != 0 and relic == relic_after:
                                raise ValueError(f"Relic is duplicated with slot: {r_af_idx+1}")
                    if 3 <= relic_index < 5:
                        for idx, relic_after in enumerate(vessel["relics"][relic_index + 1:]):
                            r_af_idx = relic_index + 1 + idx
                            if relic_after != 0 and relic == relic_after:
                                raise ValueError(f"Relic is duplicated with slot: {r_af_idx+1}")  
                else:
                    raise ValueError("Invalid item type")
        return True

    def heroes_structure_check(self, heroes: dict[int, HeroLoadout]):
        pass

    def validate_preset(self, heroes: dict[int, HeroLoadout], hero_type: int, new_preset: dict):
        _t_vessel = {"vessel_id": new_preset["vessel_id"], "relics": new_preset['relics']}
        _relics_set = set(_t_vessel["relics"])
        _relics_set.discard(0)
        if len(_relics_set) == 0:
            raise ValueError("Preset must contain at least one relic.")
        self.validate_vessel(heroes, hero_type, _t_vessel)
        for preset in heroes[hero_type].presets:
            if preset["index"] == new_preset["index"]:
                raise ValueError("Preset index duplicated. This shouldn't happen.")
            if preset["vessel_id"] == new_preset["vessel_id"] and preset["relics"] == new_preset["relics"]:
                raise ValueError(f"Preset relics combination exists. Preset Name: {preset['name']}")


class LoadoutHandler:
    """
    Hero Loadout Handler
    Manage hero loadouts, including parsing, modifying, validating, and equipping presets.
    """
    class PresetsCapacityFullError(Exception):
        pass

    _instance = None
    _initialized = False

    def __new__(cls, *args, **kwargs):
        if not cls._instance:
            cls._instance = super(LoadoutHandler, cls).__new__(cls)
        return cls._instance

    def __init__(self):
        if self._initialized:
            return
        self._initialized = True
        self.game_data = SourceDataHandler()
        self.inventory = InventoryHandler()
        self.parser = VesselParser()
        self.modifier = VesselModifier()
        self.validator = Validator()
        self.all_presets = []

    @property
    def heroes(self):
        return self.parser.heroes

    @property
    def relic_ga_hero_map(self):
        """
            Don't use this, use get_relic_equipped_by method in InventoryHandler instead
        """
        return self.parser.relic_ga_hero_map

    def get_vessel_index_in_hero(self, hero_type: int, vessel_id: int):
        if self.check_vessel(hero_type, vessel_id):
            for index, vessel in enumerate(self.heroes[hero_type].vessels):
                if vessel["vessel_id"] == vessel_id:
                    return index
        return -1

    def parse(self):
        self.parser.parse()
        self.all_presets = [p for h in self.heroes.values() for p in h.presets]
        self.all_presets.sort(key=lambda x: x["index"])

    def display_results(self):
        self.parser.display_results()

    def update_hero_loadout(self, hero_index: int):
        self.modifier.update_hero_loadout(self.heroes[hero_index])

    def update_all_loadouts(self):
        self.modifier.update_all_loadouts(self.heroes)

    def check_hero(self, hero_type: int):
        # Check if character is unlocked
        if hero_type not in range(1, 11):
            raise ValueError("Invalid hero type")
        if not self.inventory.unlock_manager.is_character_unlocked(hero_type):
            msg = f"{self.game_data.character_names[hero_type-1]} is not unlocked."
            logger.warning(msg)
            raise ValueError(msg)
        if hero_type not in self.heroes:
            raise ValueError("Hero not found. This shouldn't happen. Save file may be corrupted.")
        return True

    def check_vessel(self, hero_type: int, vessel_id: int):
        self.check_hero(hero_type)
        return any(v["vessel_id"] == vessel_id for v in self.heroes[hero_type].vessels)

    def get_vessel_id(self, hero_type: int, vessel_index: int):
        if 0 <= vessel_index < len(self.heroes[hero_type].vessels):
            return self.heroes[hero_type].vessels[vessel_index]["vessel_id"]
        else:
            raise ValueError("Invalid vessel index")

    def get_relic_ga_handle(self, hero_type: int, vessel_id: int, relic_index: int):
        if not self.check_vessel(hero_type, vessel_id):
            raise ValueError("Vessel not found")
        if 0 <= relic_index <= 5:
            for v in self.heroes[hero_type].vessels:
                if v["vessel_id"] == vessel_id:
                    return v["relics"][relic_index]
        else:
            raise ValueError("Invalid relic index")

    def equip_preset(self, hero_type: int, preset_index: int):
        self.check_hero(hero_type)
        if preset_index < len(self.all_presets):
            self.heroes[hero_type].cur_preset_idx = preset_index
            self.heroes[hero_type].cur_vessel_id = self.all_presets[preset_index]["vessel_id"]
            for vessel in self.heroes[hero_type].vessels:
                if vessel["vessel_id"] == self.heroes[hero_type].cur_vessel_id:
                    vessel["relics"] = deepcopy(self.all_presets[preset_index]["relics"])
                    break
            self.update_hero_loadout(hero_type)
        else:
            raise ValueError("Invalid preset index")

    def push_preset(self, hero_type: int, vessel_id: int, relics: list[int], name: str):
        """
        Append a new preset to the specified hero's loadout.
        
        :param hero_type: 1-based\n
            sequence: 1~10 for normal heroes, 11 for universal vessels\n
            ['Wylder', 'Guardian', 'Ironeye', 'Duchess', 'Raider',\n
             'Revenant', 'Recluse', 'Executor', 'Scholar', 'Undertaker', 'All']
        :type hero_type: int
        :param vessel_id: vessel ID Like 19001 etc.
        :type vessel_id: int
        :param relics: ga_handles
        :type relics: list[int]
        :param name: Perset Name, Max Chars 18
        :type name: str

        :returns: return the modified data as immutable bytes.
        :rtype: bytes
        """
        self.check_hero(hero_type)
        # Check Preset Capacity
        if len(self.all_presets) > 100:
            raise LoadoutHandler.PresetsCapacityFullError("Maximum preset capacity reached.")

        # Check Relics Validity

        # All Valid
        # Create a new preset
        # new preset offsets are caculated by last preset
        new_preset_offsets = {
            "base": self.all_presets[-1]["offsets"]["base"] + 80 if self.all_presets else self.parser.base_offset + 120 * 10 + 28 * 70 + 4,  # Heuristic: 10 heroes * 120 bytes + 60 vessels * 28 bytes + 4 bytes padding
            "hero_type": self.all_presets[-1]["offsets"]["base"] + 80 + 1 if self.all_presets else self.parser.base_offset + 120 * 10 + 28 * 70 + 4 + 1,
            "counter": self.all_presets[-1]["offsets"]["base"] + 80 + 3 if self.all_presets else self.parser.base_offset + 120 * 10 + 28 * 70 + 4 + 3,
            "name": self.all_presets[-1]["offsets"]["base"] + 80 + 4 if self.all_presets else self.parser.base_offset + 120 * 10 + 28 * 70 + 4 + 4,
            "vessel_id": self.all_presets[-1]["offsets"]["base"] + 80 + 44 if self.all_presets else self.parser.base_offset + 120 * 10 + 28 * 70 + 4 + 44,
            "relics": self.all_presets[-1]["offsets"]["base"] + 80 + 48 if self.all_presets else self.parser.base_offset + 120 * 10 + 28 * 70 + 4 + 48,
            "timestamp": self.all_presets[-1]["offsets"]["base"] + 80 + 72 if self.all_presets else self.parser.base_offset + 120 * 10 + 28 * 70 + 4 + 72,
        }

        new_timestamp = get_now_timestamp()

        new_preset = {
            "hero_type": hero_type,
            "index": len(self.all_presets),
            "name": name,
            "vessel_id": vessel_id,
            "relics": relics,
            "counter": 0,
            "timestamp": new_timestamp,
            "offsets": new_preset_offsets
        }
        # Check preset, if invalid will raise Exception
        self.validator.validate_preset(self.heroes, hero_type, new_preset)
        for hero in self.heroes.values():
            for preset in hero.presets:
                preset["counter"] += 1
        self.heroes[hero_type].add_preset(**new_preset)
        self.all_presets = [p for h in self.heroes.values() for p in h.presets]
        self.all_presets.sort(key=lambda x: x["index"])
        self.heroes[hero_type].auto_adjust_cur_equipment()
        self.update_all_loadouts()

    def replace_vessel_relic(self, hero_type: int, vessel_id: int,
                             relic_index: int, new_relic_ga):
        self.check_hero(hero_type)
        _new_vessel = None
        vessel_index = 0
        for idx, vessel in enumerate(self.heroes[hero_type].vessels):
            if vessel["vessel_id"] == vessel_id:
                _new_vessel = deepcopy(vessel)
                vessel_index = idx
                break
        if not _new_vessel:
            raise ValueError("Vessel not found")
        old_relic_ga = _new_vessel["relics"][relic_index]
        _new_vessel["relics"][relic_index] = new_relic_ga
        if self.validator.validate_vessel(self.heroes, hero_type, _new_vessel):
            self.heroes[hero_type].vessels[vessel_index] = _new_vessel
            # Record relic equip/unequip
            if old_relic_ga != 0:
                self.inventory.unequip_relic(old_relic_ga, hero_type)
            if new_relic_ga != 0:
                self.inventory.equip_relic(new_relic_ga, hero_type)

            if self.heroes[hero_type].cur_vessel_id == vessel_id:
                self.heroes[hero_type].auto_adjust_cur_equipment()
            self.update_hero_loadout(hero_type)
            self.parse()

    def replace_preset_relic(self, hero_type: int, relic_index: int, new_relic_ga,
                             hero_preset_index: int = -1, preset_index: int = -1):
        self.check_hero(hero_type)
        if hero_preset_index < 0 and preset_index < 0:
            raise ValueError("hero_preset_index or preset_index should be provided")
        if hero_preset_index >= 0 and preset_index >= 0:
            raise ValueError("Only one of hero_preset_index or preset_index should be provided")
        if hero_preset_index >= len(self.heroes[hero_type].presets):
            raise ValueError("Invalid preset index")
        if preset_index >= len(self.all_presets):
            raise ValueError("Invalid preset index")
        if relic_index < 0 or relic_index >= 6:
            raise ValueError("Invalid relic index")

        _new_preset = None
        if preset_index >= 0:
            _new_preset = deepcopy(self.all_presets[preset_index])
        elif hero_preset_index >= 0:
            _new_preset = deepcopy(self.heroes[hero_type].presets[hero_preset_index])
        old_relic_ga = _new_preset["relics"][relic_index]
        _new_preset["relics"][relic_index] = new_relic_ga
        _t_vessel = {"vessel_id": _new_preset["vessel_id"], "relics": _new_preset['relics']}
        self.validator.validate_vessel(self.heroes, hero_type, _t_vessel)
        if preset_index >= 0:
            self.all_presets[preset_index]['relics'][relic_index] = new_relic_ga
        elif hero_preset_index >= 0:
            self.heroes[hero_type].presets[hero_preset_index]['relics'][relic_index] = new_relic_ga
        # Record relic equip/unequip
        if old_relic_ga != 0:
            self.inventory.unequip_relic(old_relic_ga, hero_type)
        if new_relic_ga != 0:
            self.inventory.equip_relic(new_relic_ga, hero_type)

        self.heroes[hero_type].auto_adjust_cur_equipment()
        self.update_hero_loadout(hero_type)

    def export_hero_loadout(self, hero_type: int, file_path: str):
        # Export Json File with orjson package
        json_bytes = orjson.dumps(self.heroes[hero_type].get_export_data(),
                                  option=orjson.OPT_INDENT_2)
        with open(file_path, "wb") as f:
            f.write(json_bytes)

    def import_hero_loadout(self, import_file_path: str,):

        with open(import_file_path, "rb") as f:
            json_bytes = f.read()
            import_data = orjson.loads(json_bytes)
        hero_type = import_data["hero_type"]
        try:
            self.check_hero(hero_type)
        except ValueError as ve:
            return [str(ve)]

        # Set current vessel id
        im_cur_vessel_id = import_data["cur_vessel_id"]
        if self.validator.check_vessel_assignment(self.heroes, hero_type, im_cur_vessel_id):
            if is_vessel_available(im_cur_vessel_id):
                self.heroes[hero_type].cur_vessel_id = im_cur_vessel_id
            else:
                logger.warning(f"Vessel {im_cur_vessel_id} is not unlocked")
        else:
            logger.warning(f"Vessel {im_cur_vessel_id} is not assigned to hero {hero_type}.")
            logger.warning("This Loadout file may be corrupted and not safe to use.")

        # Check if All Needed Relic in Inventory
        all_needed_relics = import_data["all_needed_relics"]
        relic_info_to_ga_map = {}
        self.inventory.refresh_relics_dataframe()
        relics_df = self.inventory.relics_df
        miss_unique_names = []
        for needed_relic in all_needed_relics:
            try:
                ga_handle = relics_df[(relics_df['relic_id'] == needed_relic['relic_id']) &
                                      (relics_df['effect_1'] == needed_relic['effect_1']) &
                                      (relics_df['effect_2'] == needed_relic['effect_2']) &
                                      (relics_df['effect_3'] == needed_relic['effect_3']) &
                                      (relics_df['curse_1'] == needed_relic['curse_1']) &
                                      (relics_df['curse_2'] == needed_relic['curse_2']) &
                                      (relics_df['curse_3'] == needed_relic['curse_3'])]['ga_handle'].values[0]
            except IndexError:
                logger.info("Find needed relic not in inventory.")
                ga_handle = 0
                relic_id = needed_relic["relic_id"]
                effects = [needed_relic["effect_1"], needed_relic["effect_2"], needed_relic["effect_3"]]
                curses = [needed_relic["curse_1"], needed_relic["curse_2"], needed_relic["curse_3"]]
                if self.game_data.relics.get(relic_id):
                    if relic_id in UNIQUENESS_IDS:
                        miss_unique_names.append(self.game_data.relics[relic_id].name + ":" + self.game_data.effects[effects[0]].name + "...")
                        logger.warning(f"{self.game_data.relics[relic_id].name} is an unique relic and not in inventory.")
                    else:
                        logger.info("Found relic not in inventory, try to add it.")
                        is_deep = self.game_data.relics[relic_id].is_deep()
                        _, ga_handle = self.inventory.add_relic_to_inventory("Deep" if is_deep else "Normal")
                        self.inventory.modify_relic(ga_handle, relic_id, *effects, *curses)
            relic_info_to_ga_map[tuple(needed_relic.values())] = ga_handle

        # Reparse to correct offsets.
        self.inventory.parse()
        self.parse()

        # Transform imported relic metadata to current session ga_handles
        result_msgs = []
        transfored_data = {"presets": [],
                           "vessels": []}
        for preset in import_data["presets"]:
            try:
                relic_gas = [relic_info_to_ga_map[tuple(r.values())] for r in preset["relics"]]
                transfored_data["presets"].append({
                    "name": preset["name"],
                    "vessel_id": preset["vessel_id"],
                    "relics": relic_gas
                })
            except Exception as e:
                result_msgs.append(f"Preset {preset['name']} import failed: {e}")

        for vessel in import_data["vessels"]:
            try:
                relic_gas = [relic_info_to_ga_map.get(tuple(r.values()), 0) for r in vessel["relics"]]
                transfored_data["vessels"].append({
                    "vessel_id": vessel["vessel_id"],
                    "relics": relic_gas
                })
            except Exception as e:
                result_msgs.append(f"Vessel {vessel['vessel_id']} import failed: {e}")

        # Pause And Get selected indices
        vessel_indices, preset_indices = yield transfored_data
        if vessel_indices is None:
            vessel_indices = []
        if preset_indices is None:
            preset_indices = []

        # Import Presets
        for idx, preset in enumerate(transfored_data["presets"]):
            if idx not in preset_indices:
                result_msgs.append(f"Preset {preset['name']} import skipped.")
                continue
            if not is_vessel_available(preset['vessel_id']):
                result_msgs.append(f"Preset {preset['name']} import failed: {self.game_data.vessels[preset['vessel_id']].name} is not unlocked.")
                continue
            try:
                self.push_preset(hero_type, preset['vessel_id'], preset['relics'], preset['name'])
                result_msgs.append(f"Preset {preset['name']} imported successfully.")
            except Exception as e:
                result_msgs.append(f"Preset {preset['name']} import failed: {e}")

        # Reparse to correct offsets.
        self.parse()

        # Import Vessels
        result_msgs += self.heroes[hero_type].import_vessels(transfored_data["vessels"], vessel_indices)
        if miss_unique_names:
            result_msgs.append("="*40)
            result_msgs.append("Followed Relics are unique and cannot be added to the inventory:")
            result_msgs += miss_unique_names

        self.update_all_loadouts()
        yield result_msgs
