# -*- coding: utf-8 -*-
"""
Grid War - симулятор сражения на клеточной карте (pygame).

Файл состоит из двух независимых частей:
  1. Battle  - чистая модель (карта, юниты, группы, правила). Без pygame.
  2. App     - интерфейс pygame (редактор, симуляция, сохранение).

Правила кратко:
  * Каждый тик каждый юнит "ходит" в случайном порядке (порядок меняется каждый тик).
  * n - число тиков между ЛЮБЫМИ действиями (атака или шаг). n=1 - действие каждый тик.
  * Пехота и кавалерия: сначала атакуют соседнего врага (4 стороны), иначе идут по приказу группы.
    Кавалерия - "лучшая пехота": действует в 1.5 раза чаще (SPEED_MULT).
  * Артиллерия не двигается, стреляет строго вперёд; дальность = ART_BASE_RANGE + высота клетки.
    Выстрел идёт до первого юнита: враг - попадание, свой - выстрел заблокирован.
    Склон выше орудия закрывает обзор дальше.
  * Любое попадание убивает. Два юнита (кроме артиллерии) не могут стоять в одной клетке.
  * Перепад высот между соседними клетками больше MAX_CLIMB - обрыв, пройти нельзя.
"""
import json
import os
import random
from collections import deque

import pygame

# ============================================================ настройки
GRID_W, GRID_H = 28, 18          # размер карты в клетках
CELL = 30                        # размер клетки в пикселях
MAX_HEIGHT = 9                   # высоты 0..MAX_HEIGHT
MAX_CLIMB = 2                    # перепад выше этого - обрыв (поставьте 9, чтобы отключить)
MAX_GROUPS = 16                  # групп на армию
MAX_N = 30                       # максимум n
MAX_BRUSH = 8                    # максимальный радиус кисти
ART_BASE_RANGE = 2               # дальность артиллерии на высоте 0
RANDOM_MOVE_CHANCE = 0.02        # шанс шагнуть в случайную сторону вместо приказа
SIDESTEP_CHANCE = 0.4            # шанс обойти преграду, если путь загорожен своим
SPEED_MULT = {'infantry': 1.0, 'cavalry': 1.5, 'artillery': 1.0}
DEFAULT_N = 2
UNDO_LIMIT = 100
STALEMATE_TICKS = 300             # столько тиков без потерь - считаем тупиком

DIRS = {'N': (0, -1), 'E': (1, 0), 'S': (0, 1), 'W': (-1, 0)}
TYPES = ('infantry', 'cavalry', 'artillery')
GROUP_MODES = ('defense', 'direction', 'point')
INF = 10 ** 6

SAVE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'save.txt')


# ============================================================ модель
class Group:
    """Приказ для набора юнитов: оборона / идти в направлении / идти к точке."""
    __slots__ = ('mode', 'direction', 'target', 'n')

    def __init__(self, mode='defense', direction='E', target=None, n=DEFAULT_N):
        self.mode = mode
        self.direction = direction
        self.target = target
        self.n = n

    def to_dict(self):
        return {'mode': self.mode, 'direction': self.direction,
                'target': list(self.target) if self.target else None, 'n': self.n}

    @classmethod
    def from_dict(cls, d):
        mode = d.get('mode', 'defense')
        if mode not in GROUP_MODES:
            mode = 'defense'
        direction = d.get('direction', 'E')
        if direction not in DIRS:
            direction = 'E'
        target = None
        t = d.get('target')
        if isinstance(t, (list, tuple)) and len(t) == 2:
            tx, ty = int(t[0]), int(t[1])
            if 0 <= tx < GRID_W and 0 <= ty < GRID_H:
                target = (tx, ty)
        n = int(d.get('n', d.get('speed', DEFAULT_N)))    # 'speed' - старый формат
        return cls(mode, direction, target, max(1, min(MAX_N, n)))


class Unit:
    __slots__ = ('army', 'utype', 'group', 'x', 'y', 'direction', 'charge', 'dead')

    def __init__(self, army, utype, group, x, y, direction='E'):
        self.army = army
        self.utype = utype
        self.group = group          # индекс группы в своей армии; None у артиллерии
        self.x, self.y = x, y
        self.direction = direction  # куда смотрит (важно только для артиллерии)
        self.charge = 0.0           # накопленная "готовность к действию"
        self.dead = False

    def to_dict(self):
        return {'army': self.army, 'utype': self.utype, 'group': self.group,
                'x': self.x, 'y': self.y, 'direction': self.direction,
                'charge': self.charge}


class Battle:
    def __init__(self):
        self.heights = [[0] * GRID_W for _ in range(GRID_H)]
        self.groups = [[Group()], [Group()]]
        self.art_n = [DEFAULT_N, DEFAULT_N]       # n артиллерии каждой армии
        self.units = []
        self.cells = []                           # cells[y][x] -> список юнитов в клетке
        self.alive = [0, 0]
        self.terrain_ver = 0                      # растёт при любом изменении рельефа
        self.tick = 0
        self.casualties = [0, 0]
        self.last_kill_tick = 0
        self.events = []                          # (is_shell, x0, y0, x1, y1) для эффектов UI
        self.start_state = None                   # состояние на момент старта симуляции
        self._flow = {}
        self._flow_ver = -1
        self.rebuild_index()

    # ---------------------------------------------------- индекс клеток
    def rebuild_index(self):
        self.cells = [[[] for _ in range(GRID_W)] for _ in range(GRID_H)]
        self.alive = [0, 0]
        for u in self.units:
            if not u.dead:
                self.cells[u.y][u.x].append(u)
                self.alive[u.army] += 1

    def occupied(self, x, y):
        """Есть ли в клетке юнит с коллизией (артиллерия не мешает)."""
        for v in self.cells[y][x]:
            if v.utype != 'artillery':
                return True
        return False

    # ---------------------------------------------------- редактор
    @staticmethod
    def disc(cx, cy, r):
        r2 = r * r
        for y in range(max(0, cy - r), min(GRID_H, cy + r + 1)):
            for x in range(max(0, cx - r), min(GRID_W, cx + r + 1)):
                if (x - cx) ** 2 + (y - cy) ** 2 <= r2:
                    yield x, y

    def paint_height(self, cx, cy, r, delta, done):
        """Меняет высоту круглой кистью. `done` - клетки, уже тронутые этим мазком."""
        changed = False
        for x, y in self.disc(cx, cy, r):
            if (x, y) in done:
                continue
            done.add((x, y))
            h = self.heights[y][x]
            nh = max(0, min(MAX_HEIGHT, h + delta))
            if nh != h:
                self.heights[y][x] = nh
                changed = True
        if changed:
            self.terrain_ver += 1

    def flatten(self):
        self.heights = [[0] * GRID_W for _ in range(GRID_H)]
        self.terrain_ver += 1

    def place_units(self, cx, cy, r, army, utype, group, facing):
        if utype != 'artillery' and not (0 <= group < len(self.groups[army])):
            return
        for x, y in self.disc(cx, cy, r):
            cell = self.cells[y][x]
            if utype == 'artillery':
                if any(v.utype == 'artillery' for v in cell):
                    continue
                u = Unit(army, utype, None, x, y, facing)
            else:
                if any(v.utype != 'artillery' for v in cell):
                    continue
                u = Unit(army, utype, group, x, y)
            self.units.append(u)
            cell.append(u)
            self.alive[army] += 1

    def erase_units(self, cx, cy, r):
        area = set(self.disc(cx, cy, r))
        self.units = [u for u in self.units if (u.x, u.y) not in area]
        self.rebuild_index()

    def clear_units(self):
        self.units = []
        self.rebuild_index()

    def add_group(self, army):
        if len(self.groups[army]) >= MAX_GROUPS:
            return None
        self.groups[army].append(Group())
        return len(self.groups[army]) - 1

    def delete_group(self, army, idx):
        """Удаляет группу; её юниты переходят в соседнюю. Последнюю группу удалить нельзя."""
        if len(self.groups[army]) <= 1 or not (0 <= idx < len(self.groups[army])):
            return False
        self.groups[army].pop(idx)
        merge_to = idx - 1 if idx > 0 else 0
        for u in self.units:
            if u.army == army and u.group is not None:
                if u.group == idx:
                    u.group = merge_to
                elif u.group > idx:
                    u.group -= 1
        return True

    def stats(self):
        """(по типам, по группам) для каждой армии - за один проход."""
        by_type = [{t: 0 for t in TYPES} for _ in range(2)]
        by_group = [[0] * len(self.groups[a]) for a in range(2)]
        for u in self.units:
            by_type[u.army][u.utype] += 1
            if u.group is not None:
                by_group[u.army][u.group] += 1
        return by_type, by_group

    # ---------------------------------------------------- симуляция
    def period(self, u):
        if u.utype == 'artillery':
            return self.art_n[u.army]
        return self.groups[u.army][u.group].n

    def start(self):
        self.start_state = self.state_dict()
        self.reset()

    def reset(self):
        self.load_state(self.start_state)
        self.tick = 0
        self.casualties = [0, 0]
        self.last_kill_tick = 0
        self.events.clear()
        for u in self.units:                       # разводим фазы, чтобы все не били в один тик
            u.charge = float(random.randrange(self.period(u)))

    def winner(self):
        """None - бой идёт, 0/1 - победила армия, -1 - ничья."""
        a0, a1 = self.alive
        if a0 and a1:
            return None
        return 0 if a0 else 1 if a1 else -1

    def stalled(self):
        """Долго нет потерь: армии разошлись или стоят, бой больше не развивается."""
        return self.winner() is None and self.tick - self.last_kill_tick >= STALEMATE_TICKS

    def step(self):
        order = self.units[:]
        random.shuffle(order)                      # порядок ходов - заново каждый тик
        for u in order:
            if not u.dead:
                self.act(u)
        self.units = [u for u in self.units if not u.dead]
        self.tick += 1

    def act(self, u):
        n = self.period(u)
        u.charge += SPEED_MULT[u.utype]
        if u.charge < n:
            return                                 # ожидание: ничего не происходит
        u.charge = min(u.charge - n, n)
        if not self.attack(u):
            self.move(u)

    # ---- атака
    def attack(self, u):
        t = self.artillery_target(u) if u.utype == 'artillery' else self.melee_target(u)
        if t is None:
            return False
        self.kill(t, u)
        return True

    def kill(self, t, by):
        t.dead = True
        self.cells[t.y][t.x].remove(t)
        self.alive[t.army] -= 1
        self.casualties[t.army] += 1
        self.last_kill_tick = self.tick
        if len(self.events) < 400:
            self.events.append((by.utype == 'artillery', by.x, by.y, t.x, t.y))

    def melee_target(self, u):
        found = []
        for dx, dy in ((0, 0), (0, -1), (1, 0), (0, 1), (-1, 0)):
            x, y = u.x + dx, u.y + dy
            if 0 <= x < GRID_W and 0 <= y < GRID_H:
                for v in self.cells[y][x]:
                    if v.army != u.army:
                        found.append(v)
        return random.choice(found) if found else None

    def fire_lane(self, u):
        """Клетки, до которых долетает снаряд (дальность и рельеф, без учёта юнитов)."""
        h0 = self.heights[u.y][u.x]
        dx, dy = DIRS[u.direction]
        lane = []
        x, y = u.x, u.y
        for _ in range(ART_BASE_RANGE + h0):
            x += dx
            y += dy
            if not (0 <= x < GRID_W and 0 <= y < GRID_H):
                break
            lane.append((x, y))
            if self.heights[y][x] > h0:            # склон выше орудия закрывает обзор
                break
        return lane

    def artillery_target(self, u):
        for x, y in self.fire_lane(u):
            cell = self.cells[y][x]
            if not cell:
                continue
            enemies = [v for v in cell if v.army != u.army]
            return random.choice(enemies) if enemies else None   # свой - выстрел заблокирован
        return None

    # ---- движение
    def can_step(self, x, y, nx, ny):
        if not (0 <= nx < GRID_W and 0 <= ny < GRID_H):
            return False
        return abs(self.heights[ny][nx] - self.heights[y][x]) <= MAX_CLIMB

    def try_step(self, u, dx, dy):
        nx, ny = u.x + dx, u.y + dy
        if not self.can_step(u.x, u.y, nx, ny) or self.occupied(nx, ny):
            return False
        self.cells[u.y][u.x].remove(u)
        self.cells[ny][nx].append(u)
        u.x, u.y = nx, ny
        return True

    def move(self, u):
        if u.utype == 'artillery':
            return
        g = self.groups[u.army][u.group]
        if g.mode == 'defense':
            return
        if random.random() < RANDOM_MOVE_CHANCE:   # случайный шаг: ломает ровные шеренги
            dirs = list(DIRS.values())
            random.shuffle(dirs)
            for dx, dy in dirs:
                if self.try_step(u, dx, dy):
                    break
            return
        if g.mode == 'direction':
            self.move_direction(u, g)
        else:
            self.move_to_point(u, g)

    def move_direction(self, u, g):
        dx, dy = DIRS[g.direction]
        if not (0 <= u.x + dx < GRID_W and 0 <= u.y + dy < GRID_H):
            return                                  # упёрлись в край карты
        if self.try_step(u, dx, dy):
            return
        if random.random() < SIDESTEP_CHANCE:       # путь закрыт: пробуем обойти сбоку
            side = [(dy, dx), (-dy, -dx)]
            random.shuffle(side)
            for sx, sy in side:
                if self.try_step(u, sx, sy):
                    return

    def move_to_point(self, u, g):
        if not g.target:
            return
        dist = self.flow(g.target)
        d = dist[u.y][u.x]
        if d == 0 or d >= INF:
            return                                  # уже на месте или дойти нельзя
        closer, other = [], []
        for dx, dy in DIRS.values():
            nx, ny = u.x + dx, u.y + dy
            if 0 <= nx < GRID_W and 0 <= ny < GRID_H and dist[ny][nx] < INF \
                    and not self.occupied(nx, ny):
                (closer if dist[ny][nx] < d else other).append((dx, dy))
        if closer:
            dx, dy = random.choice(closer)
            self.try_step(u, dx, dy)
        elif other and random.random() < SIDESTEP_CHANCE:   # проход занят своими - обходим
            dx, dy = random.choice(other)
            self.try_step(u, dx, dy)

    def flow(self, target):
        """Карта расстояний до точки (с учётом обрывов, без учёта юнитов). Кэшируется."""
        if self._flow_ver != self.terrain_ver:
            self._flow, self._flow_ver = {}, self.terrain_ver
        dist = self._flow.get(target)
        if dist is None:
            dist = [[INF] * GRID_W for _ in range(GRID_H)]
            tx, ty = target
            dist[ty][tx] = 0
            q = deque([(tx, ty)])
            while q:
                x, y = q.popleft()
                d = dist[y][x] + 1
                for dx, dy in DIRS.values():
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < GRID_W and 0 <= ny < GRID_H and dist[ny][nx] == INF \
                            and self.can_step(x, y, nx, ny):
                        dist[ny][nx] = d
                        q.append((nx, ny))
            self._flow[target] = dist
        return dist

    # ---------------------------------------------------- сохранение / загрузка
    def state_dict(self):
        """Редактируемая часть состояния (карта, армии). Годится и для undo."""
        return {
            'heights': [r[:] for r in self.heights],
            'art_n': list(self.art_n),
            'groups': {str(a): [g.to_dict() for g in self.groups[a]] for a in (0, 1)},
            'units': [u.to_dict() for u in self.units],
        }

    @staticmethod
    def _parse_state(d):
        if not isinstance(d, dict):
            raise ValueError('неверный формат файла')
        hs = d.get('heights')
        if not isinstance(hs, list) or len(hs) != GRID_H or \
                any(not isinstance(r, list) or len(r) != GRID_W for r in hs):
            raise ValueError('размер карты в файле не %dx%d' % (GRID_W, GRID_H))
        try:
            heights = [[max(0, min(MAX_HEIGHT, int(v))) for v in r] for r in hs]
            art_raw = d.get('art_n', [DEFAULT_N, DEFAULT_N])
            art_n = [max(1, min(MAX_N, int(art_raw[a]))) for a in (0, 1)]

            raw = d.get('groups', {})
            groups, gid_map = [[], []], [{}, {}]
            for a in (0, 1):
                lst = raw.get(str(a), raw.get(a, []))
                lst = sorted(lst, key=lambda g: g.get('gid', 0))     # старый формат: gid
                for i, gd in enumerate(lst[:MAX_GROUPS]):
                    groups[a].append(Group.from_dict(gd))
                    gid_map[a][gd.get('gid', i)] = i
                if not groups[a]:
                    groups[a].append(Group())

            units, taken, arty = [], set(), set()
            for ud in d.get('units', []):
                army, utype = int(ud['army']), ud['utype']
                x, y = int(ud['x']), int(ud['y'])
                if army not in (0, 1) or utype not in TYPES \
                        or not (0 <= x < GRID_W and 0 <= y < GRID_H):
                    continue
                facing = ud.get('direction', 'E')
                if facing not in DIRS:
                    facing = 'E'
                if utype == 'artillery':
                    if (x, y) in arty:
                        continue
                    arty.add((x, y))
                    u = Unit(army, utype, None, x, y, facing)
                else:
                    if (x, y) in taken:
                        continue
                    taken.add((x, y))
                    u = Unit(army, utype, gid_map[army].get(ud.get('group'), 0), x, y)
                u.charge = max(0.0, float(ud.get('charge', 0)))
                units.append(u)
        except (KeyError, TypeError, ValueError, AttributeError, IndexError):
            raise ValueError('повреждённые данные в файле')
        return heights, art_n, groups, units

    def load_state(self, d):
        heights, art_n, groups, units = self._parse_state(d)   # сначала проверка, потом замена
        self.heights, self.art_n, self.groups, self.units = heights, art_n, groups, units
        self.rebuild_index()
        self.terrain_ver += 1

    def save_dict(self, in_sim):
        d = self.state_dict()
        d['version'] = 2
        if in_sim and self.start_state:
            d['sim'] = {'tick': self.tick, 'casualties': list(self.casualties),
                        'start': self.start_state}
        return d

    def load_dict(self, d):
        """Возвращает True, если файл содержал состояние посреди симуляции."""
        sim = d.get('sim') if isinstance(d, dict) else None
        if sim:
            try:
                start = sim['start']
                tick, cas = int(sim['tick']), [int(c) for c in sim['casualties']][:2]
                if len(cas) != 2:
                    raise ValueError
            except (KeyError, TypeError, ValueError):
                raise ValueError('повреждённые данные симуляции')
            self._parse_state(start)                           # проверка
        self.load_state(d)
        self.events.clear()
        if sim:
            self.start_state, self.tick, self.casualties = sim['start'], tick, cas
            self.last_kill_tick = tick
            return True
        self.start_state, self.tick, self.casualties = None, 0, [0, 0]
        return False


# ============================================================ интерфейс
PANEL_W = 360
BAR_H = 130
MAP_W, MAP_H = GRID_W * CELL, GRID_H * CELL
WIDTH, HEIGHT = MAP_W + PANEL_W, MAP_H + BAR_H
FPS = 60
SPEEDS = (1, 2, 4, 6, 10, 15, 30, 60)       # тиков в секунду
FX_FRAMES = 12                              # сколько кадров живёт вспышка выстрела/удара

BG = (24, 26, 32)
PANEL_BG = (38, 41, 52)
BAR_BG = (30, 32, 40)
BTN = (62, 67, 84)
BTN_ACTIVE = (84, 120, 200)
BTN_OFF = (48, 50, 60)
GREEN = (46, 125, 80)
TXT = (232, 232, 236)
DIM = (150, 155, 172)
WARN = (240, 180, 70)
ERR = (240, 100, 100)
GRID_COLOR = (20, 22, 26)
CLIFF_COLOR = (95, 22, 22)
ARMY_COLORS = ((70, 130, 255), (255, 85, 85))
ARMY_DARK = ((50, 95, 190), (190, 60, 60))

DIR_RU = {'N': 'Север', 'E': 'Восток', 'S': 'Юг', 'W': 'Запад'}
DIR_SHORT = {'N': 'С', 'E': 'В', 'S': 'Ю', 'W': 'З'}
TYPE_RU = {'infantry': 'Пехота', 'cavalry': 'Кавалерия', 'artillery': 'Артиллерия'}
MODE_RU = {'defense': 'Оборона', 'direction': 'Направление', 'point': 'К точке'}
TOOL_HELP = {
    'terrain': 'ЛКМ - поднять на 1 (можно вести мышью), ПКМ - опустить. Колесо - радиус кисти.',
    'unit': 'ЛКМ - поставить юнитов в выбранную группу, ПКМ - стереть. Колесо - радиус кисти.',
    'target': 'ЛКМ - задать точку для выбранной группы, ПКМ - убрать точку.',
}
SIM_HELP = 'Пробел - пауза, N - один тик, R - сначала, Esc - вернуться в редактор.'

_STOPS = [(0, (80, 160, 80)), (3, (210, 200, 90)), (6, (175, 120, 70)), (9, (235, 235, 235))]


def height_color(h):
    for (h0, c0), (h1, c1) in zip(_STOPS, _STOPS[1:]):
        if h0 <= h <= h1:
            t = (h - h0) / (h1 - h0)
            return tuple(int(c0[i] + (c1[i] - c0[i]) * t) for i in range(3))
    return _STOPS[-1][1]


HEIGHT_COLORS = [height_color(min(h, 9)) for h in range(MAX_HEIGHT + 1)]

FONTS = {}
_TEXT_CACHE = {}


def init_fonts():
    names = 'segoeui,arial,dejavusans,liberationsans,freesans,notosans,ubuntu,consolas'

    def make(size, bold=False):
        path = pygame.font.match_font(names, bold=bold)
        return pygame.font.Font(path, size) if path else pygame.font.Font(None, size + 6)

    FONTS.update(main=make(14), small=make(12), big=make(19, True), tiny=make(11, True))


def render_text(s, color, font='main'):
    s = s or ' '                      # pygame не любит рендерить пустую строку
    key = (s, color, font)
    img = _TEXT_CACHE.get(key)
    if img is None:
        if len(_TEXT_CACHE) > 600:
            _TEXT_CACHE.clear()
        img = _TEXT_CACHE[key] = FONTS[font].render(s, True, color)
    return img


def lighten(c, k=18):
    return tuple(min(255, v + k) for v in c)


# ------------------------------------------------------------ виджеты
class Btn:
    __slots__ = ('rect', 'label', 'action', 'active', 'hint', 'color', 'enabled', 'active_color')

    def __init__(self, rect, label, action, active, hint, color, enabled, active_color):
        self.rect, self.label, self.action = rect, label, action
        self.active, self.hint, self.color, self.enabled = active, hint, color, enabled
        self.active_color = active_color


class UI:
    """Мини-GUI: виджеты собираются заново каждый кадр (immediate mode)."""

    def __init__(self):
        self.buttons, self.texts, self.bars = [], [], []

    def clear(self):
        self.buttons, self.texts, self.bars = [], [], []

    def text(self, pos, s, color=TXT, font='main', center=False):
        self.texts.append((pos, s, color, font, center))

    def bar(self, rect, frac, color):
        self.bars.append((pygame.Rect(rect), max(0.0, min(1.0, frac)), color))

    def button(self, rect, label, action, active=False, hint='', color=None, enabled=True,
               active_color=None):
        self.buttons.append(Btn(pygame.Rect(rect), label, action, active, hint, color, enabled,
                                active_color))

    def click(self, pos):
        for b in self.buttons:
            if b.enabled and b.rect.collidepoint(pos):
                b.action()
                return True
        return False

    def hint_at(self, pos):
        for b in self.buttons:
            if b.rect.collidepoint(pos):
                return b.hint
        return ''

    def draw(self, surf, mouse):
        for pos, s, color, font, center in self.texts:
            img = render_text(s, color, font)
            surf.blit(img, img.get_rect(center=pos) if center else img.get_rect(topleft=pos))
        for rect, frac, color in self.bars:
            pygame.draw.rect(surf, (20, 22, 28), rect, border_radius=3)
            if frac > 0:
                pygame.draw.rect(surf, color, (rect.x, rect.y, max(2, int(rect.w * frac)), rect.h),
                                 border_radius=3)
        for b in self.buttons:
            if not b.enabled:
                col = BTN_OFF
            elif b.active:
                col = b.active_color or BTN_ACTIVE
            else:
                col = b.color or BTN
            if b.enabled and b.rect.collidepoint(mouse):
                col = lighten(col)
            pygame.draw.rect(surf, col, b.rect, border_radius=5)
            pygame.draw.rect(surf, (14, 15, 20), b.rect, 1, border_radius=5)
            img = render_text(b.label, TXT if b.enabled else (110, 112, 125), 'main')
            surf.blit(img, img.get_rect(center=b.rect.center))


class Panel:
    """Вертикальная раскладка виджетов правой панели."""
    ROW = 28

    def __init__(self, ui, x, y, w):
        self.ui, self.x, self.y, self.w = ui, x, y, w

    def gap(self, h=8):
        self.y += h

    def title(self, s):
        self.ui.text((self.x, self.y), s, TXT, 'big')
        self.y += 30

    def heading(self, s):
        self.ui.text((self.x, self.y + 1), s, DIM, 'small')
        self.y += 18

    def line(self, s, color=DIM, font='small'):
        self.ui.text((self.x, self.y), s, color, font)
        self.y += 17

    def button(self, label, action, **kw):
        self.ui.button((self.x, self.y, self.w, self.ROW), label, action, **kw)
        self.y += self.ROW + 4

    def row(self, items):
        """items: [(label, action, {kwargs})]"""
        k = len(items)
        bw = (self.w - 6 * (k - 1)) // k
        for i, (label, action, kw) in enumerate(items):
            self.ui.button((self.x + i * (bw + 6), self.y, bw, self.ROW), label, action, **kw)
        self.y += self.ROW + 4

    def seg(self, options, current, on_select, colors=None, hints=None):
        items = []
        for val, label in options:
            kw = {'active': val == current}
            if colors and val in colors:
                kw['active_color'] = colors[val]
            if hints and val in hints:
                kw['hint'] = hints[val]
            items.append((label, lambda v=val: on_select(v), kw))
        self.row(items)

    def stepper(self, label, value, on_dec, on_inc, can_dec=True, can_inc=True, hint=''):
        """Подпись слева, справа:  [-]  значение  [+]"""
        r, right = self.y, self.x + self.w
        self.ui.text((self.x, r + 6), label, TXT, 'main')
        self.ui.button((right - 30, r, 30, self.ROW), '+', on_inc, hint=hint, enabled=can_inc)
        self.ui.text((right - 66, r + self.ROW // 2), value, TXT, 'main', center=True)
        self.ui.button((right - 132, r, 30, self.ROW), '-', on_dec, hint=hint, enabled=can_dec)
        self.y += self.ROW + 4


# ------------------------------------------------------------ рисование юнитов
def draw_shape(surf, utype, cx, cy, r, col, outline=(0, 0, 0), width=1):
    """Пехота - квадрат, кавалерия - треугольник, артиллерия - ромб."""
    if utype == 'infantry':
        rr = int(r * 0.75)
        rect = (cx - rr, cy - rr, 2 * rr, 2 * rr)
        pygame.draw.rect(surf, col, rect)
        pygame.draw.rect(surf, outline, rect, width)
    elif utype == 'cavalry':
        pts = [(cx, cy - r), (cx - r, cy + r - 2), (cx + r, cy + r - 2)]
        pygame.draw.polygon(surf, col, pts)
        pygame.draw.polygon(surf, outline, pts, width)
    else:
        pts = [(cx, cy - r), (cx + r, cy), (cx, cy + r), (cx - r, cy)]
        pygame.draw.polygon(surf, col, pts)
        pygame.draw.polygon(surf, outline, pts, width)


def cell_center(x, y):
    return x * CELL + CELL // 2, y * CELL + CELL // 2


# ------------------------------------------------------------ приложение
class App:
    def __init__(self, screen):
        self.screen = screen
        self.battle = Battle()
        self.ui = UI()
        self.quit = False
        self.mode = 'edit'                    # 'edit' | 'sim'
        self.running = False
        self.speed_i = 3
        self.acc = 0.0
        self.stall_seen = None
        # настройки редактора
        self.tool = 'terrain'                 # terrain | unit | target
        self.army = 0
        self.utype = 'infantry'
        self.facing = 'E'
        self.brush = 1
        self.sel = [0, 0]                     # выбранная группа каждой армии
        self.undo_stack = []
        self.stroke = None
        self.toast = None
        self.fx = []
        self._tsurf, self._tver = None, -1
        self.lane_tile = pygame.Surface((CELL, CELL), pygame.SRCALPHA)
        self.lane_tile.fill((255, 220, 0, 55))
        self.brush_tile = pygame.Surface((CELL, CELL), pygame.SRCALPHA)
        self.brush_tile.fill((255, 255, 255, 60))
        self.build_panel()

    # ---------------------------------------------------- утилиты
    def say(self, text, color=TXT, ms=3500):
        self.toast = (text, pygame.time.get_ticks() + ms, color)

    def cur_group(self):
        return self.battle.groups[self.army][self.sel[self.army]]

    def clamp_sel(self):
        for a in (0, 1):
            self.sel[a] = max(0, min(len(self.battle.groups[a]) - 1, self.sel[a]))

    def commit(self, before):
        """Кладёт состояние `before` в историю, если с тех пор что-то изменилось."""
        if self.battle.state_dict() != before:
            self.undo_stack.append(before)
            del self.undo_stack[:-UNDO_LIMIT]

    def do(self, fn, *args):
        """Выполняет изменение карты/армий так, чтобы его можно было отменить."""
        before = self.battle.state_dict()
        fn(*args)
        self.commit(before)

    def undo(self):
        if self.mode != 'edit' or not self.undo_stack:
            return
        self.battle.load_state(self.undo_stack.pop())
        self.clamp_sel()
        self.say('Действие отменено')

    # ---------------------------------------------------- действия редактора
    def set_tool(self, t):
        self.tool = t

    def set_army(self, a):
        self.army = a

    def set_utype(self, t):
        self.utype = t

    def set_facing(self, d):
        self.facing = d

    def change_brush(self, d):
        self.brush = max(0, min(MAX_BRUSH, self.brush + d))

    def shift_group(self, d):
        a = self.army
        self.sel[a] = (self.sel[a] + d) % len(self.battle.groups[a])

    def add_group(self):
        i = self.battle.add_group(self.army)
        if i is None:
            self.say('Максимум групп в армии: %d' % MAX_GROUPS, WARN)
        else:
            self.sel[self.army] = i

    def delete_group(self):
        a = self.army
        if self.battle.delete_group(a, self.sel[a]):
            self.clamp_sel()
            self.say('Группа удалена, её юниты перешли в соседнюю')
        else:
            self.say('Единственную группу удалить нельзя', WARN)

    def set_mode(self, m):
        g = self.cur_group()
        g.mode = m
        if m == 'point' and g.target is None:
            self.tool = 'target'
            self.say('Кликните по карте, чтобы выбрать точку для группы')

    def set_dir(self, d):
        self.cur_group().direction = d

    def change_n(self, delta):
        g = self.cur_group()
        g.n = max(1, min(MAX_N, g.n + delta))

    def change_art_n(self, delta):
        a = self.army
        self.battle.art_n[a] = max(1, min(MAX_N, self.battle.art_n[a] + delta))

    # ---------------------------------------------------- мазки мышью
    def cell_at(self, pos):
        x, y = pos[0] // CELL, pos[1] // CELL
        if pos[0] >= 0 and pos[1] >= 0 and 0 <= x < GRID_W and 0 <= y < GRID_H:
            return x, y
        return None

    def begin_stroke(self, button, cell):
        self.stroke = {'button': button, 'before': self.battle.state_dict(),
                       'done': set(), 'last': None}
        if self.tool == 'target':
            g = self.cur_group()
            if button == 1:
                g.mode, g.target = 'point', cell
            else:
                g.target = None
            self.end_stroke()
            return
        self.stroke_move(cell)

    def stroke_move(self, cell):
        s = self.stroke
        if s is None or cell is None or cell == s['last']:
            return
        s['last'] = cell
        x, y = cell
        b = self.battle
        if self.tool == 'terrain':
            b.paint_height(x, y, self.brush, 1 if s['button'] == 1 else -1, s['done'])
        elif self.tool == 'unit':
            if s['button'] == 1:
                b.place_units(x, y, self.brush, self.army, self.utype,
                              self.sel[self.army], self.facing)
            else:
                b.erase_units(x, y, self.brush)

    def end_stroke(self):
        if self.stroke:
            self.commit(self.stroke['before'])
            self.stroke = None

    # ---------------------------------------------------- управление симуляцией
    def start_sim(self):
        if self.mode != 'edit':
            return
        if min(self.battle.alive) == 0:
            self.say('Поставьте юнитов обеих армий, чтобы начать бой', WARN)
            return
        self.end_stroke()
        self.battle.start()
        self.mode, self.running, self.acc = 'sim', True, 0.0
        self.stall_seen = None
        self.fx.clear()

    def to_editor(self):
        if self.mode != 'sim':
            return
        self.battle.load_state(self.battle.start_state)
        self.battle.start_state = None
        self.battle.tick, self.battle.casualties = 0, [0, 0]
        self.mode, self.running = 'edit', False
        self.clamp_sel()
        self.fx.clear()
        self.undo_stack.clear()

    def reset_sim(self):
        if self.mode != 'sim':
            return
        self.battle.reset()
        self.running, self.acc = False, 0.0
        self.stall_seen = None
        self.fx.clear()

    def toggle_run(self):
        if self.mode == 'edit':
            self.start_sim()
        elif self.battle.winner() is None:
            self.running = not self.running

    def step_once(self):
        if self.mode == 'sim' and not self.running and self.battle.winner() is None:
            self.battle.step()
            self.after_step()

    def change_speed(self, d):
        self.speed_i = max(0, min(len(SPEEDS) - 1, self.speed_i + d))

    def after_step(self):
        for ev in self.battle.events:
            self.fx.append(list(ev) + [FX_FRAMES])
        self.battle.events.clear()
        del self.fx[:-300]
        b = self.battle
        w = b.winner()
        if w is not None and self.running:
            self.running = False
            self.say('Ничья: никого не осталось' if w == -1 else 'Победа: армия %d' % (w + 1), WARN, 8000)
        elif b.stalled() and self.running and self.stall_seen != b.last_kill_tick:
            self.stall_seen = b.last_kill_tick           # пауза один раз на каждый тупик
            self.running = False
            self.say('Тупик: %d тиков без потерь. Пробел - продолжить, R - сначала.'
                     % STALEMATE_TICKS, WARN, 10000)

    # ---------------------------------------------------- сохранение
    def save(self):
        try:
            with open(SAVE_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.battle.save_dict(self.mode == 'sim'), f, ensure_ascii=False)
            self.say('Сохранено: ' + os.path.basename(SAVE_FILE))
        except OSError as e:
            self.say('Не удалось сохранить: %s' % e, ERR)

    def load(self):
        try:
            with open(SAVE_FILE, encoding='utf-8') as f:
                data = json.load(f)
            in_sim = self.battle.load_dict(data)
        except FileNotFoundError:
            self.say('Файл %s не найден - сначала сохраните' % os.path.basename(SAVE_FILE), WARN)
            return
        except (OSError, ValueError) as e:
            self.say('Не удалось загрузить: %s' % e, ERR)
            return
        self.end_stroke()
        self.mode, self.running, self.acc = ('sim' if in_sim else 'edit'), False, 0.0
        self.undo_stack.clear()
        self.fx.clear()
        self.stall_seen = None
        self.clamp_sel()
        self.say('Загружено' + (' (симуляция на паузе)' if in_sim else ''))

    # ---------------------------------------------------- события
    def handle(self, e):
        if e.type == pygame.QUIT:
            self.quit = True
        elif e.type == pygame.KEYDOWN:
            self.on_key(e)
        elif e.type == pygame.MOUSEBUTTONDOWN:
            if e.button not in (1, 3):
                return                                    # колесо и средняя кнопка - не клики
            if e.pos[0] < MAP_W:
                self.end_stroke()                         # на случай, если отпускание кнопки потерялось
                cell = self.cell_at(e.pos)
                if self.mode == 'edit' and cell:
                    self.begin_stroke(e.button, cell)
            elif e.button == 1:
                self.ui.click(e.pos)
        elif e.type == pygame.MOUSEMOTION:
            if self.stroke:
                self.stroke_move(self.cell_at(e.pos))
        elif e.type == pygame.MOUSEBUTTONUP:
            if self.stroke and e.button == self.stroke['button']:
                self.end_stroke()
        elif e.type == pygame.MOUSEWHEEL:
            if self.mode == 'edit' and self.tool != 'target':
                self.change_brush(1 if e.y > 0 else -1 if e.y < 0 else 0)

    def on_key(self, e):
        ctrl = pygame.key.get_mods() & pygame.KMOD_CTRL
        k = e.key
        if ctrl and k == pygame.K_z:
            self.undo()
        elif ctrl and k == pygame.K_s:
            self.save()
        elif ctrl and k == pygame.K_l:
            self.load()
        elif k == pygame.K_SPACE:
            self.toggle_run()
        elif self.mode == 'sim':
            if k == pygame.K_r:
                self.reset_sim()
            elif k == pygame.K_n:
                self.step_once()
            elif k == pygame.K_ESCAPE:
                self.to_editor()
        else:
            tools = {pygame.K_1: 'terrain', pygame.K_2: 'unit', pygame.K_3: 'target'}
            if k in tools:
                self.tool = tools[k]

    # ---------------------------------------------------- обновление
    def update(self, dt):
        for f in self.fx:
            f[5] -= 1
        self.fx = [f for f in self.fx if f[5] > 0]
        if self.mode == 'sim' and self.running:
            interval = 1.0 / SPEEDS[self.speed_i]
            self.acc += dt
            steps = 0
            while self.acc >= interval and steps < 12:
                self.acc -= interval
                self.battle.step()
                steps += 1
                if self.battle.winner() is not None:
                    break
            if steps >= 12:
                self.acc = 0.0                  # не копим отставание, если компьютер не успевает
            self.after_step()

    # ---------------------------------------------------- правая панель
    def build_panel(self):
        self.ui.clear()
        p = Panel(self.ui, MAP_W + 12, 10, PANEL_W - 24)
        if self.mode == 'edit':
            self.panel_edit(p)
        else:
            self.panel_sim(p)
        return p.y

    def panel_edit(self, p):
        b, a = self.battle, self.army
        by_type, by_group = b.stats()
        p.title('Редактор')
        p.button('Старт симуляции  [Пробел]', self.start_sim, color=GREEN,
                 hint='Запустить бой. Нужны юниты обеих армий; редактор вернётся по Esc.')

        p.heading('Инструмент  [1] [2] [3]')
        p.seg([('terrain', 'Рельеф'), ('unit', 'Юниты'), ('target', 'Цель')],
              self.tool, self.set_tool,
              hints={'terrain': TOOL_HELP['terrain'], 'unit': TOOL_HELP['unit'],
                     'target': TOOL_HELP['target']})
        if self.tool != 'target':
            p.stepper('Радиус кисти', str(self.brush), lambda: self.change_brush(-1),
                      lambda: self.change_brush(1), self.brush > 0, self.brush < MAX_BRUSH,
                      'Радиус 0 - одна клетка. Колесо мыши тоже меняет радиус.')
        p.gap(4)

        p.heading('Армия')
        p.seg([(0, 'Армия 1'), (1, 'Армия 2')], a, self.set_army,
              colors={0: ARMY_DARK[0], 1: ARMY_DARK[1]})
        t = by_type[a]
        p.line('Юнитов: %d  (пехота %d, кавалерия %d, артиллерия %d)'
               % (b.alive[a], t['infantry'], t['cavalry'], t['artillery']))
        if self.tool == 'unit':
            p.heading('Что ставить')
            p.seg([('infantry', 'Пехота'), ('cavalry', 'Кавалерия'), ('artillery', 'Артиллерия')],
                  self.utype, self.set_utype,
                  hints={'cavalry': 'Кавалерия - лучшая пехота: действует в %.1f раза чаще.'
                                    % SPEED_MULT['cavalry'],
                         'artillery': 'Артиллерия не двигается, стреляет прямо; дальность растёт с высотой.'})
            if self.utype == 'artillery':
                p.seg([(d, DIR_RU[d]) for d in 'NESW'], self.facing, self.set_facing,
                      hints={d: 'Куда будет стрелять поставленная артиллерия' for d in 'NESW'})
        p.gap(4)

        n_groups = len(b.groups[a])
        i = self.sel[a]
        g = b.groups[a][i]
        p.heading('Группы армии %d (пехота и кавалерия)' % (a + 1))
        gh = 'Новые юниты попадают в выбранную группу, она подсвечена на карте белой рамкой.'
        p.stepper('Группа', '%d / %d' % (i + 1, n_groups), lambda: self.shift_group(-1),
                  lambda: self.shift_group(1), n_groups > 1, n_groups > 1, gh)
        p.row([('Новая группа', lambda: self.do(self.add_group),
                {'hint': 'Добавить группу (максимум %d).' % MAX_GROUPS,
                 'enabled': n_groups < MAX_GROUPS}),
               ('Удалить группу', lambda: self.do(self.delete_group),
                {'hint': 'Юниты удалённой группы перейдут в соседнюю.',
                 'enabled': n_groups > 1})])
        p.seg([(m, MODE_RU[m]) for m in GROUP_MODES], g.mode,
              lambda m: self.do(self.set_mode, m),
              hints={'defense': 'Стоит на месте, бьёт соседних врагов.',
                     'direction': 'Бьёт врага рядом, иначе идёт в заданную сторону.',
                     'point': 'Бьёт врага рядом, иначе идёт к точке в обход обрывов.'})
        if g.mode == 'direction':
            p.seg([(d, DIR_RU[d]) for d in 'NESW'], g.direction,
                  lambda d: self.do(self.set_dir, d))
        elif g.mode == 'point':
            if g.target:
                p.line('Цель: (%d, %d)' % g.target, TXT, 'main')
            else:
                p.line('Цель не задана - группа будет стоять', WARN, 'main')
            p.button('Выбрать цель на карте', lambda: self.set_tool('target'),
                     active=self.tool == 'target', hint=TOOL_HELP['target'])
        p.stepper('Действие раз в n тиков', str(g.n), lambda: self.do(self.change_n, -1),
                  lambda: self.do(self.change_n, 1), g.n > 1, g.n < MAX_N,
                  'n - тиков между ЛЮБЫМИ действиями (шаг или атака). n=1 - каждый тик.')
        p.line('В этой группе юнитов: %d' % by_group[a][i])
        p.stepper('Артиллерия армии, n', str(b.art_n[a]), lambda: self.do(self.change_art_n, -1),
                  lambda: self.do(self.change_art_n, 1), b.art_n[a] > 1, b.art_n[a] < MAX_N,
                  'Артиллерия стреляет раз в n тиков (отдельно для каждой армии).')
        p.gap(4)

        p.row([('Отмена', self.undo, {'enabled': bool(self.undo_stack),
                                      'hint': 'Отменить последнее изменение [Ctrl+Z].'}),
               ('Без юнитов', lambda: self.do(b.clear_units),
                {'hint': 'Убрать всех юнитов обеих армий (можно отменить).'}),
               ('Без рельефа', lambda: self.do(b.flatten),
                {'hint': 'Обнулить все высоты (можно отменить).'})])
        p.row([('Сохранить', self.save, {'hint': 'Сохранить в save.txt [Ctrl+S].'}),
               ('Загрузить', self.load, {'hint': 'Загрузить из save.txt [Ctrl+L].'})])

    def panel_sim(self, p):
        b = self.battle
        w = b.winner()
        p.title('Симуляция')
        if w is not None:
            p.line('Ничья' if w == -1 else 'Победила армия %d' % (w + 1), WARN, 'main')
        elif b.stalled():
            p.line('Пауза: тупик, %d тиков без потерь' % (b.tick - b.last_kill_tick), WARN, 'main')
        else:
            p.line('Бой идёт' if self.running else 'Пауза', TXT, 'main')
        p.gap(2)
        p.row([('Пауза  [Пробел]' if self.running else 'Старт  [Пробел]', self.toggle_run,
                {'enabled': w is None, 'color': GREEN}),
               ('Шаг  [N]', self.step_once,
                {'enabled': w is None and not self.running, 'hint': 'Выполнить один тик на паузе.'})])
        p.row([('Сначала  [R]', self.reset_sim, {'hint': 'Вернуть расстановку на момент старта.'}),
               ('В редактор  [Esc]', self.to_editor, {})])
        p.stepper('Скорость, тиков/с', str(SPEEDS[self.speed_i]), lambda: self.change_speed(-1),
                  lambda: self.change_speed(1), self.speed_i > 0, self.speed_i < len(SPEEDS) - 1)
        p.line('Тик: %d' % b.tick, TXT, 'main')
        p.gap(4)

        by_type, by_group = b.stats()
        for a in (0, 1):
            col = ARMY_COLORS[a]
            p.ui.text((p.x, p.y), 'Армия %d' % (a + 1), col, 'big')
            right = render_text('живых %d, потери %d' % (b.alive[a], b.casualties[a]), TXT, 'small')
            p.ui.text((p.x + p.w - right.get_width(), p.y + 4),
                      'живых %d, потери %d' % (b.alive[a], b.casualties[a]), TXT, 'small')
            p.y += 24
            total = b.alive[a] + b.casualties[a]
            p.ui.bar((p.x, p.y, p.w, 8), b.alive[a] / total if total else 0, col)
            p.y += 14
            t = by_type[a]
            p.line('Пехота %d   Кавалерия %d   Артиллерия %d'
                   % (t['infantry'], t['cavalry'], t['artillery']))
            groups = b.groups[a]
            half = (p.w - 6) // 2
            for i, g in enumerate(groups):
                if g.mode == 'defense':
                    short = 'оборона'
                elif g.mode == 'direction':
                    short = 'на ' + DIR_SHORT[g.direction]
                else:
                    short = 'к (%d,%d)' % g.target if g.target else 'к ?'
                p.ui.text((p.x + (i % 2) * (half + 6), p.y + (i // 2) * 15),
                          'Г%d %s n%d: %d' % (i + 1, short, g.n, by_group[a][i]), DIM, 'small')
            p.y += ((len(groups) + 1) // 2) * 15 + 8
        p.row([('Сохранить', self.save, {'hint': 'Сохранить текущее состояние боя [Ctrl+S].'}),
               ('Загрузить', self.load, {'hint': 'Загрузить из save.txt [Ctrl+L].'})])

    # ---------------------------------------------------- рисование карты
    def terrain(self):
        b = self.battle
        if self._tsurf is None or self._tver != b.terrain_ver:
            s = pygame.Surface((MAP_W, MAP_H))
            for y in range(GRID_H):
                for x in range(GRID_W):
                    h = b.heights[y][x]
                    s.fill(HEIGHT_COLORS[h], (x * CELL, y * CELL, CELL, CELL))
                    if h:
                        s.blit(render_text(str(h), (20, 20, 20), 'tiny'), (x * CELL + 3, y * CELL + 2))
            for x in range(GRID_W + 1):
                pygame.draw.line(s, GRID_COLOR, (x * CELL, 0), (x * CELL, MAP_H))
            for y in range(GRID_H + 1):
                pygame.draw.line(s, GRID_COLOR, (0, y * CELL), (MAP_W, y * CELL))
            for y in range(GRID_H):                       # обрывы - толстые тёмные линии
                for x in range(GRID_W):
                    h = b.heights[y][x]
                    if x + 1 < GRID_W and abs(b.heights[y][x + 1] - h) > MAX_CLIMB:
                        pygame.draw.line(s, CLIFF_COLOR, ((x + 1) * CELL, y * CELL),
                                         ((x + 1) * CELL, (y + 1) * CELL), 4)
                    if y + 1 < GRID_H and abs(b.heights[y + 1][x] - h) > MAX_CLIMB:
                        pygame.draw.line(s, CLIFF_COLOR, (x * CELL, (y + 1) * CELL),
                                         ((x + 1) * CELL, (y + 1) * CELL), 4)
            self._tsurf, self._tver = s, b.terrain_ver
        return self._tsurf

    def draw_unit(self, u, highlight):
        cx, cy = cell_center(u.x, u.y)
        col = ARMY_COLORS[u.army]
        r = CELL // 2 - 3
        draw_shape(self.screen, u.utype, cx, cy, r, col,
                   (255, 255, 255) if highlight else (0, 0, 0), 2 if highlight else 1)
        if u.utype == 'artillery':
            dx, dy = DIRS[u.direction]
            pygame.draw.line(self.screen, (255, 235, 80), (cx, cy),
                             (cx + dx * (CELL // 2 - 1), cy + dy * (CELL // 2 - 1)), 3)
            return
        g = self.battle.groups[u.army][u.group]
        if g.mode == 'direction':                      # метка направления
            dx, dy = DIRS[g.direction]
            pygame.draw.line(self.screen, (255, 255, 170), (cx + dx * (r - 2), cy + dy * (r - 2)),
                             (cx + dx * (CELL // 2 - 1), cy + dy * (CELL // 2 - 1)), 3)
        num = render_text(str(u.group + 1), (255, 255, 255), 'tiny')
        self.screen.blit(num, num.get_rect(center=(cx, cy + (3 if u.utype == 'cavalry' else 0))))

    def draw_map(self, mouse):
        s, b = self.screen, self.battle
        s.blit(self.terrain(), (0, 0))
        arty = [u for u in b.units if u.utype == 'artillery']
        for u in arty:                                  # зона огня артиллерии
            for x, y in b.fire_lane(u):
                s.blit(self.lane_tile, (x * CELL, y * CELL))

        edit = self.mode == 'edit'
        for a in (0, 1):                                # маркеры целей групп
            for i, g in enumerate(b.groups[a]):
                if g.mode == 'point' and g.target:
                    cx, cy = cell_center(*g.target)
                    chosen = edit and a == self.army and i == self.sel[a]
                    pygame.draw.circle(s, (20, 20, 24), (cx, cy), 10)
                    pygame.draw.circle(s, (255, 255, 255) if chosen else ARMY_COLORS[a], (cx, cy), 10, 2)
                    num = render_text(str(i + 1), ARMY_COLORS[a], 'tiny')
                    s.blit(num, num.get_rect(center=(cx, cy)))

        def chosen_unit(u):
            return (edit and self.tool != 'terrain' and u.army == self.army
                    and u.group is not None and u.group == self.sel[u.army])

        for u in arty:
            self.draw_unit(u, False)
        for u in b.units:
            if u.utype != 'artillery':
                self.draw_unit(u, chosen_unit(u))

        for is_shell, x0, y0, x1, y1, ttl in self.fx:   # вспышки выстрелов и ударов
            p0, p1 = cell_center(x0, y0), cell_center(x1, y1)
            pygame.draw.line(s, (255, 235, 80) if is_shell else (255, 255, 255), p0, p1,
                             3 if is_shell else 2)
            r = 7
            pygame.draw.line(s, (255, 40, 40), (p1[0] - r, p1[1] - r), (p1[0] + r, p1[1] + r), 3)
            pygame.draw.line(s, (255, 40, 40), (p1[0] - r, p1[1] + r), (p1[0] + r, p1[1] - r), 3)

        cell = self.cell_at(mouse) if mouse[0] < MAP_W else None
        if edit and cell:                               # курсор / кисть
            if self.tool == 'target':
                pygame.draw.rect(s, (255, 255, 0), (cell[0] * CELL, cell[1] * CELL, CELL, CELL), 2)
            else:
                for x, y in b.disc(cell[0], cell[1], self.brush):
                    s.blit(self.brush_tile, (x * CELL, y * CELL))

        w = b.winner()
        if self.mode == 'sim' and w is not None:        # баннер победы
            shade = pygame.Surface((MAP_W, 70), pygame.SRCALPHA)
            shade.fill((0, 0, 0, 170))
            s.blit(shade, (0, MAP_H // 2 - 35))
            text = 'Ничья' if w == -1 else 'Победила армия %d' % (w + 1)
            img = FONTS['big'].render(text, True, (255, 255, 255) if w == -1 else ARMY_COLORS[w])
            s.blit(img, img.get_rect(center=(MAP_W // 2, MAP_H // 2)))

    # ---------------------------------------------------- нижняя строка состояния
    def cell_info(self, cell):
        x, y = cell
        b = self.battle
        s = 'Клетка (%d, %d), высота %d' % (x, y, b.heights[y][x])
        names = []
        for u in b.cells[y][x]:
            n = '%s армии %d' % (TYPE_RU[u.utype], u.army + 1)
            if u.group is not None:
                n += ', группа %d' % (u.group + 1)
            names.append(n)
        return s + ('   |   ' + '; '.join(names) if names else '')

    def draw_bar(self, mouse):
        s = self.screen
        pygame.draw.rect(s, BAR_BG, (0, MAP_H, MAP_W, BAR_H))
        pygame.draw.line(s, (0, 0, 0), (0, MAP_H), (MAP_W, MAP_H), 2)
        cell = self.cell_at(mouse) if mouse[0] < MAP_W else None
        info = self.cell_info(cell) if cell else 'Наведите курсор на клетку'
        s.blit(render_text(info, TXT, 'main'), (10, MAP_H + 9))

        now = pygame.time.get_ticks()
        if self.toast and now < self.toast[1]:
            text, color = self.toast[0], self.toast[2]
        else:
            text = self.ui.hint_at(mouse) or (SIM_HELP if self.mode == 'sim' else TOOL_HELP[self.tool])
            color = DIM
        s.blit(render_text(text, color, 'small'), (10, MAP_H + 36))

        # легенда
        y = MAP_H + BAR_H - 30
        x = 12
        for utype, label in (('infantry', 'Пехота'), ('cavalry', 'Кавалерия (быстрее)'),
                             ('artillery', 'Артиллерия')):
            draw_shape(s, utype, x + 8, y + 10, 8, (170, 175, 190))
            img = render_text(label, DIM, 'small')
            s.blit(img, (x + 22, y + 3))
            x += 22 + img.get_width() + 18
        pygame.draw.rect(s, (255, 220, 0), (x, y + 4, 16, 12), 1)
        img = render_text('Зона огня', DIM, 'small')
        s.blit(img, (x + 22, y + 3))
        x += 22 + img.get_width() + 18
        pygame.draw.line(s, CLIFF_COLOR, (x, y + 2), (x, y + 18), 4)
        s.blit(render_text('Обрыв (не пройти)', DIM, 'small'), (x + 10, y + 3))

    def draw(self):
        mouse = pygame.mouse.get_pos()
        self.screen.fill(BG)
        self.build_panel()
        self.draw_map(mouse)
        self.draw_bar(mouse)
        pygame.draw.rect(self.screen, PANEL_BG, (MAP_W, 0, PANEL_W, HEIGHT))
        pygame.draw.line(self.screen, (0, 0, 0), (MAP_W, 0), (MAP_W, HEIGHT), 2)
        self.ui.draw(self.screen, mouse)


# ============================================================ запуск
def main():
    pygame.init()
    pygame.font.init()
    init_fonts()
    flags = getattr(pygame, 'SCALED', 0) | getattr(pygame, 'RESIZABLE', 0)
    try:
        screen = pygame.display.set_mode((WIDTH, HEIGHT), flags)
    except pygame.error:
        screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption('Grid War - симуляция сражения')
    app = App(screen)
    clock = pygame.time.Clock()
    while not app.quit:
        dt = clock.tick(FPS) / 1000.0
        for e in pygame.event.get():
            app.handle(e)
        app.update(dt)
        app.draw()
        pygame.display.flip()
    pygame.quit()


if __name__ == '__main__':
    main()
