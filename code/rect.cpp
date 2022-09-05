// c++ -std=c++20 -O3 -o solve solve.cpp
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
#define STB_IMAGE_IMPLEMENTATION
#include "stb/stb_image.h"
#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb/stb_image_write.h"

using std::abs;
using std::clog;
using std::cout;
using std::endl;
using std::min;
using std::size_t;
using std::sort;
using std::stringstream;
using std::string;
using std::unordered_map;
using std::vector;


typedef uint8_t u8;
typedef uint32_t u32;
typedef int32_t i32;
typedef float r32;
typedef float r64;

static constexpr const u32 u32_max = std::numeric_limits<u32>::max();


typedef union __attribute__((packed)) {
    struct {
        u8 r,g,b,a;
    };
    u32 value;
} rgba;


typedef struct {
    u32 w, h;
    rgba* px;
} image;


typedef struct {
    u32 l, t, r, b;
} ltrb;


static constexpr const u32 ROOT_ID = 0xffffffff;

typedef struct block {
    u32 id;
    u32 x,y,w,h;
    vector<rgba> px;
    vector<struct block> children;
} block;


typedef struct {
    u32 last_id;
    block root;
} prog_state;


typedef struct {
    vector<string> lines;
    u32 cost;
} program;

static program _Program;


static void
program_append(program& prog, const string& line, u32 cost) {
    prog.lines.push_back(line);
    prog.cost += cost;
}


static void
program_print(program& prog) {
    for (auto& line : prog.lines) {
        cout << line << endl;
    }
}


typedef vector<u32> id_path;


bool operator == (const rgba& a, const rgba& b) {
    return a.r == b.r && a.g == b.g && a.b == b.b && a.a == b.a;
}


template<>
struct std::hash<rgba> {
    size_t operator () (const rgba& p) const {
        std::hash<u32> h;
        return h(p.value);
    }
};


std::ostream& operator << (std::ostream& so, const rgba& px) {
    so << "[" << u32(px.r) << "," << u32(px.g) << "," << u32(px.b) << "," << u32(px.a) << "]";
    return so;
}


std::ostream& operator << (std::ostream& so, const ltrb& r) {
    so << "{" << r.l << "," << r.t << "," << r.r << "," << r.b << "}";
    return so;
}


std::ostream& operator << (std::ostream& so, const id_path& v) {
    so << "[";
    for (auto it = v.begin(); it != v.end(); ) {
        so << *it++;
        if (it != v.end()) {
            so << ".";
        }
    }
    so << "]";
    return so;
}


std::ostream& operator << (std::ostream& so, const block& r) {
    so << "{id:" << r.id << " [" << r.x << "," << r.y << "," << r.w << "," << r.h << "]}";
    return so;
}


static u32
eval_cost(const prog_state& state, u32 base_cost, const block& r) {
    const auto& root = state.root;
    r64 canvas = root.w * root.h;
    r64 block = r.w * r.h;
    return round(r64(base_cost) * canvas / block);
}


static u8
select_at(block& r, const id_path& sel, block** pr) {
    if (sel.size() == 0) { return 0; }
    for (auto& q : r.children) {
        if (q.id == sel[0]) {
            if (sel.size() == 1) {
                *pr = &q;
                return 1;
            }
            else {
                id_path subsel(sel.begin() + 1, sel.end());
                return select_at(q, subsel, pr);
            }
        }
    }
    return 0;
}


static u8
select_at0(block& r, const id_path& sel, block** pr) {
    if (sel.size() > 0) {
        u8 res = select_at(r, sel, pr);
        if (!res) { return 0; }
    }
    else {
        *pr = &r;
    }
    return 1;
}


static u8
select_leaf(block& r, const id_path& sel, block** pr) {
    block* qr = nullptr;
    u8 res = select_at(r, sel, &qr);
    if (!res) { return 0; }
    if (qr->children.size() > 0) { return 0; }
    *pr = qr;
    return 1;
}


static id_path
path_to_px(const block& r, u32 x, u32 y) {
    auto inner = [] (const block& r, u32 x, u32 y) -> id_path {
        id_path path;
        auto inner = [&path] (const auto& inner, const block& r, u32 x, u32 y) -> u8 {
            for (auto& q : r.children) {
                if (y >= q.y && y < q.y + q.h && x >= q.x && x < q.x + q.w) {
                    path.push_back(q.id);
                    if (q.children.size() == 0) {
                        return 1;
                    }
                    u8 res = inner(inner, q, x, y);
                    if (res) { return 1; }
                }
            }
            return 0;
        };
        u8 res = inner(inner, r, x, y);
        if (!res) {
            clog << "no path to " << x << "," << y << endl;
        }
        if (!res) { return {}; }
        // clog << "path to " << x << "," << y << ": " << path << endl;
        return path;
    };
    return inner(r, x, y);
}


static void
block_pop_id(block& r, u32 id) {
    vector<block> children;
    for (auto& child : r.children) {
        if (child.id != id) {
            children.push_back(child);
        }
    }
    r.children = children;
}


static void
block_purge_empty(block& r) {
    if (r.children.size() > 0) {
        for (auto& q : r.children) {
            block_purge_empty(q);
        }
        vector<block> children;
        for (auto& child : r.children) {
            if (child.children.size() != 0 || child.px.size() != 0) {
                children.push_back(child);
            }
        }
        r.children = children;
    }
}


static u8
op_color(prog_state& state, const id_path& sel, const rgba& c) {
    // clog << "color " << sel << " " << c << endl;
    block* pr = nullptr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { return 0; }
    pr->px.assign(pr->px.size(), c);

    stringstream so; so << "color " << sel << " " << c;
    program_append(_Program, so.str(), eval_cost(state, 5, *pr));
    return 1;
}


static u8
op_cut_x(prog_state& state, const id_path& sel, u32 cx) {
    // clog << "cut " << sel << " [x] ["  << cx << "]" << endl;
    block* pr = nullptr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { return 0; }
    block& r = *pr;
    if (cx <= r.x || cx >= r.x + r.w) { return 0; }
    r.children = {
        {.id=0, .x=r.x, .y=r.y, .w=cx-r.x, .h=r.h},
        {.id=1, .x=cx, .y=r.y, .w=r.x+r.w-cx, .h=r.h},
    };
    for (auto& q : r.children) {
        vector<rgba> v(q.w * q.h);
        for (u32 y = 0, oy = q.y - r.y, ox = q.x - r.x; y < q.h; ++y) {
            for (u32 x = 0; x < q.w; ++x) {
                v[y * q.w + x] = r.px[(oy + y) * r.w + (ox + x)];
            }
        }
        q.px = v;
    }
    r.px.clear();

    stringstream so; so << "cut " << sel << " [x] ["  << cx << "]";
    program_append(_Program, so.str(), eval_cost(state, 7, *pr));
    return 1;
}


static u8
op_cut_y(prog_state& state, const id_path& sel, u32 cy) {
    // clog << "cut " << sel << " [y] ["  << cy << "]" << endl;
    block* pr = nullptr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { clog << "! no leaf " << sel << endl; }
    if (!res) { return 0; }
    block& r = *pr;
    if (cy <= r.y || cy >= r.y + r.h) { clog << "! out of bounds cy:" << cy << " " << r << endl; }
    if (cy <= r.y || cy >= r.y + r.h) { return 0; }
    r.children = {
        {.id=0, .x=r.x, .y=r.y, .w=r.w, .h=cy-r.y},
        {.id=1, .x=r.x, .y=cy, .w=r.w, .h=r.y+r.h-cy},
    };
    for (auto& q : r.children) {
        vector<rgba> v(q.w * q.h);
        for (u32 y = 0, oy = q.y - r.y, ox = q.x - r.x; y < q.h; ++y) {
            for (u32 x = 0; x < q.w; ++x) {
                v[y * q.w + x] = r.px[(oy + y) * r.w + (ox + x)];
            }
        }
        q.px = v;
    }
    r.px.clear();

    stringstream so; so << "cut " << sel << " [y] ["  << cy << "]";
    program_append(_Program, so.str(), eval_cost(state, 7, *pr));
    return 1;
}


static u8
op_cut_p(prog_state& state, const id_path& sel, u32 cx, u32 cy) {
    // clog << "cut " << sel << " ["  << cx << "," << cy << "]" << endl;
    block* pr = nullptr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { return 0; }
    block& r = *pr;
    if (cx < r.x || cx >= r.x + r.w || cy < r.y || cy >= r.y + r.h) { return 0; }
    r.children = {
        {.id=0, .x=r.x, .y=r.y, .w=cx-r.x, .h=cy-r.y},
        {.id=1, .x=cx, .y=r.y, .w=r.x+r.w-cx, .h=cy-r.y},
        {.id=2, .x=cx, .y=cy, .w=r.x+r.w-cx, .h=r.y+r.h-cy},
        {.id=3, .x=r.x, .y=cy, .w=cx-r.x, .h=r.y+r.h-cy},
    };
    for (auto& q : r.children) {
        vector<rgba> v(q.w * q.h);
        for (u32 y = 0, oy = q.y - r.y, ox = q.x - r.x; y < q.h; ++y) {
            for (u32 x = 0; x < q.w; ++x) {
                v[y * q.w + x] = r.px[(oy + y) * r.w + (ox + x)];
            }
        }
        q.px = v;
    }
    r.px.clear();

    stringstream so; so << "cut " << sel << " ["  << cx << "," << cy << "]";
    program_append(_Program, so.str(), eval_cost(state, 10, *pr));
    return 1;
}


static u8
op_merge(prog_state& state, const id_path& sela, const id_path& selb) {
    // clog << "merge " << sela << " " << selb << endl;
    u8 res;
    block *parenta, *parentb, *pa, *pb;
    u32 ida, idb;
    {
        res = select_leaf(state.root, sela, &pa);
        if (!res) { return 0; }
        res = select_leaf(state.root, selb, &pb);
        if (!res) { return 0; }
        auto psela = sela;
        psela.pop_back();
        res = select_at0(state.root, psela, &parenta);
        if (!res) { return 0; }
        auto pselb = selb;
        pselb.pop_back();
        res = select_at0(state.root, pselb, &parentb);
        if (!res) { return 0; }
        ida = pa->id;
        idb = pb->id;
    }
    block big = (pa->w * pa->h < pb->w * pb->h) ? *pb : *pa;

    if (pa->x == pb->x) {
        if (pa->w != pb->w) { return 0; }
        if (pa->y < pb->y) {
            if (pa->y + pa->h != pb->y) { return 0; }
        }
        else {
            if (pb->y + pb->h != pa->y) { return 0; }
        }
    }
    else if (pa->y == pb->y) {
        if (pa->h != pb->h) { return 0; }
        if (pa->x < pb->x) {
            if (pa->x + pa->w != pb->x) { return 0; }
        }
        else {
            if (pb->x + pb->w != pa->x) { return 0; }
        }
    }
    else {
        return 0;
    }

    u32 id = state.last_id + 1;

    block m = {
        .id = id,
        .x = min(pa->x, pb->x),
        .y = min(pa->y, pb->y),
        .w = ((pa->x == pb->x) ? (pa->w) : (pa->w + pb->w)),
        .h = ((pa->x == pb->x) ? (pa->h + pb->h) : (pa->h)),
    };
    m.px.resize(m.w * m.h);
    for (u32 y = 0, oy = pa->y - m.y, ox = pa->x - m.x; y < pa->h; ++y) {
        for (u32 x = 0; x < pa->w; ++x) {
            m.px[(oy + y) * m.w + (ox + x)] = pa->px[y * pa->w + x];
        }
    }
    for (u32 y = 0, oy = pb->y - m.y, ox = pb->x - m.x; y < pb->h; ++y) {
        for (u32 x = 0; x < pb->w; ++x) {
            m.px[(oy + y) * m.w + (ox + x)] = pb->px[y * pb->w + x];
        }
    }

    block_pop_id(*parenta, ida);
    block_pop_id(*parentb, idb);
    block_purge_empty(state.root);

    state.last_id = id;
    auto& root = state.root;
    root.children.push_back(m);

    stringstream so; so << "merge " << sela << " " << selb;
    program_append(_Program, so.str(), eval_cost(state, 1, big));
    return 1;
}


static void
dump_state(prog_state& state) {
#if 1
    clog << "----" << endl;
    clog << "last id: " << state.last_id << endl;

    auto inner = [] (const block& r, u32 level) -> void {
        auto inner = [] (const auto& inner, const block& r, u32 level) -> void {
            if (r.id != ROOT_ID) {
                clog << string(level * 2, ' ') << r.id << ": ";
                clog << "(" << r.x << "," << r.y << "," << r.w << "," << r.h << ")";
                clog << endl;
            }
            else {
                clog << string(level * 2, ' ') << "root:" << endl;
            }
            for (auto& q : r.children) {
                inner(inner, q, level + 1);
            }
        };
        inner(inner, r, level);
    };

    inner(state.root, 0);
#endif
#if 1
    clog << "program:" << endl;
    program_print(_Program);
#endif
    clog << "--" << endl;
}


static u8
ops_fill_rect_v(prog_state& state, const id_path& sel, const ltrb& r, const rgba& c) {
    // clog << "rect_v " << sel << " " << r << " " << c << endl;

    block* pr;
    u8 res = select_at(state.root, sel, &pr);
    if (!res) { return 0; }

    auto subsel = sel;
    if (r.l <= pr->x && r.r >= pr->x + pr->w) {
    }
    else if (r.l <= pr->x) {
        res = op_cut_x(state, subsel, r.r);
        if (!res) { return 0; }
        subsel.push_back(0);
    }
    else if (r.r >= pr->x + pr->w) {
        res = op_cut_x(state, subsel, r.l);
        if (!res) { return 0; }
        subsel.push_back(1);
    }
    if (r.t > pr->y) {
        res = op_cut_y(state, subsel, r.t);
        if (!res) { return 0; }
        subsel.push_back(1);
    }
    if (r.b < pr->y + pr->h) {
        res = op_cut_y(state, subsel, r.b);
        if (!res) { return 0; }
        subsel.push_back(0);
    }
    res = op_color(state, subsel, c);
    if (!res) { return 0; }

#if 0
    auto a = subsel;
    auto b = subsel;
    b.back() = 1 - subsel.back();
    res = op_merge(state, a, b);
    if (!res) { return 0; }
    while (subsel.size() > 2) {
        subsel.pop_back();
        b = subsel;
        b.back() = 1 - subsel.back();
        res = op_merge(state, {state.last_id}, b);
        if (!res) { return 0; }
    }
#endif
    return 1;
}


static u8
ops_fill_rect_h(prog_state& state, const id_path& sel, const ltrb& r, const rgba& c) {
    // clog << "rect_h " << sel << " " << r << " " << c << endl;

    block* pr;
    u8 res = select_at(state.root, sel, &pr);
    if (!res) { return 0; }

    auto subsel = sel;
    if (r.t <= pr->y && r.b >= pr->y + pr->h) {
    }
    else if (r.t <= pr->y) {
        res = op_cut_y(state, subsel, r.b);
        if (!res) { return 0; }
        subsel.push_back(0);
    }
    else if (r.b >= pr->y + pr->h) {
        res = op_cut_y(state, subsel, r.t);
        if (!res) { return 0; }
        subsel.push_back(1);
    }
    if (r.l > pr->x) {
        res = op_cut_x(state, subsel, r.l);
        if (!res) { return 0; }
        subsel.push_back(1);
    }
    if (r.r < pr->x + pr->w) {
        res = op_cut_x(state, subsel, r.r);
        if (!res) { return 0; }
        subsel.push_back(0);
    }
    res = op_color(state, subsel, c);
    if (!res) { return 0; }

#if 0
    auto a = subsel;
    auto b = subsel;
    b.back() = 1 - subsel.back();
    res = op_merge(state, a, b);
    if (!res) { return 0; }
    while (subsel.size() > 2) {
        subsel.pop_back();
        b = subsel;
        b.back() = 1 - subsel.back();
        res = op_merge(state, {state.last_id}, b);
        if (!res) { return 0; }
    }
#endif
    return 1;
}


static u8
ops_fill_rect_two_point(prog_state& state, const id_path& sel, const ltrb& r, const rgba& c) {
    // clog << "rect_2p " << sel << " " << r << " " << c << endl;

    u8 res = op_cut_p(state, sel, r.r, r.t);
    if (!res) { return 0; }

    id_path subsel = sel;
    subsel.push_back(3);
    res = op_cut_p(state, subsel, r.l, r.b);
    if (!res) { return 0; }

    subsel.push_back(1);
    op_color(state, subsel, c);

#if 0
    u32 base = state.last_id;
    auto a = subsel;
    auto b = subsel;
    a.back() = 0;
    b.back() = 1;
    res = op_merge(state, a, b);
    if (!res) { return 0; }

    a.back() = 2;
    b.back() = 3;
    res = op_merge(state, a, b);
    if (!res) { return 0; }

    res = op_merge(state, {base+1}, {base+2});
    if (!res) { return 0; }

    subsel.pop_back();
    a = subsel;
    b = subsel;
    a.back() = 2;
    res = op_merge(state, a, {base+3});
    if (!res) { return 0; }

    a.back() = 0;
    b.back() = 1;
    res = op_merge(state, a, b);
    if (!res) { return 0; }

    res = op_merge(state, {base+4}, {base+5});
    if (!res) { return 0; }
#endif
    return 1;
}


static u8
ops_fill_rect(prog_state& state, const id_path& sel, const ltrb& r, const rgba& c) {
    // clog << "fill_rect " << sel << " " << r << " " << c << endl;

    block* pr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { return 0; }

    if (r.l <= pr->x || r.r >= pr->x + pr->w) {
        return ops_fill_rect_v(state, sel, r, c);
    }
    else if (r.t <= pr->y || r.b >= pr->y + pr->h) {
        return ops_fill_rect_h(state, sel, r, c);
    }
    else {
        return ops_fill_rect_two_point(state, sel, r, c);
    }
}


static void
image_fill_rect(image& im, const block& r) {
    if (r.children.size() > 0) {
        for (auto& p : r.children) {
            image_fill_rect(im, p);
        }
    }
    else {
        auto it = r.px.begin();
        for (u32 y = 0; y < r.h; ++y) {
            for (u32 x = 0, ox = (y + r.y) * im.w + r.x; x < r.w; ++x) {
                im.px[ox + x] = *it++;
            }
        }
    }
}


static void
image_flip_vertically(image& im) {
    for (u32 y = 0; y < im.h / 2; ++y) {
        for (u32 x = 0; x < im.w; ++x) {
            rgba& a = im.px[y * im.w + x];
            rgba& b = im.px[(im.h - y - 1) * im.w + x];
            rgba t = a;
            a = b;
            b = t;
        }
    }
}


static unordered_map<rgba, u32>
image_histogram(const image& im) {
    const u32 w = im.w;
    const u32 h = im.h;
    unordered_map<rgba, u32> histos;
    for (u32 y = 0; y < h; ++y) {
        for (u32 x = 0; x < w; ++x) {
            rgba c = im.px[y * w + x];
            histos[c] += 1;
        }
    }
    return histos;
}


static vector<rgba>
image_palette(const image& im) {
    auto histos = image_histogram(im);
    vector<rgba> palette;
    for (auto& [k, n] : histos) {
        palette.push_back(k);
    }
    sort(palette.begin(), palette.end(), [&histos] (const rgba& a, const rgba& b) {
        return histos[b] < histos[a];
    });
    return palette;
}


static r64
pixel_dist(const rgba& p, const rgba& q) {
    r64 r = i32(p.r) - i32(q.r);
    r64 g = i32(p.g) - i32(q.g);
    r64 b = i32(p.b) - i32(q.b);
    r64 a = i32(p.a) - i32(q.a);
    return sqrt(r * r + g * g + b * b + a * a);
}


static u32
image_dist(const image& a, const image& b) {
    if (a.w != b.w || a.h != b.h) { return u32_max; }
    auto *pa = a.px, *pb = b.px;
    r64 diff = 0;
    const r64 alpha = 0.005;
    for (u32 y = 0; y < a.h; ++y) {
        for (u32 x = 0; x < a.w; ++x) {
            diff += pixel_dist(*pa++, *pb++);
        }
    }
    return round(diff * alpha);
}


static u8
similar(const rgba& p, const rgba& q, r64 w = 0) {
    return pixel_dist(p, q) <= w;
}


typedef struct {
    r64 px_dist;
} opt_state;


static void
solve(prog_state& state, const image& task, const opt_state& opt) {
    auto& root = state.root;
    const u32 w = root.w;
    const u32 h = root.h;

    u8 visited[w][h];
    memset(visited, 0, w * h);

    auto palette = image_palette(task);
    const rgba bg = palette[0];
    // constexpr const rgba bg = {255,255,255,255};
    op_color(state, {0}, bg);

    for (u32 oy = 0; oy < h; ++oy) {
        for (u32 ox = 0; ox < w; ++ox) {
            if (visited[oy][ox]) { continue; }
            const rgba c = task.px[oy * w + ox];
            if (similar(c, bg, opt.px_dist)) { continue; }
            id_path osel = path_to_px(state.root, ox, oy);
            if (osel.size() == 0) { dump_state(state); }
            if (osel.size() == 0) { return; }

            vector<u8> mr, mg, mb, ma;
            u32 x = ox;
            for (; x < w; ++x) {
                id_path tsel = path_to_px(state.root, x, oy);
                if (tsel.size() == 0) { dump_state(state); }
                if (tsel.size() == 0) { return; }
                if (tsel != osel) { break; }
                rgba k = task.px[oy * w + x];
                if (!similar(c, k, opt.px_dist)) { break; }
                mr.push_back(c.r);
                mg.push_back(c.g);
                mb.push_back(c.b);
                ma.push_back(c.a);
            }
            u32 ow = x - ox;
            u32 y = oy + 1;
            u32 ok = 1;
            for (; ok && (y < h); ++y) {
                for (u32 x = 0; x < ow; ++x) {
                    block* pr;
                    id_path tsel = path_to_px(state.root, ox+x, y);
                    if (tsel.size() == 0) { dump_state(state); }
                    if (tsel.size() == 0) { return; }
                    if (tsel != osel) {
                        ok = 0;
                        break;
                    }

                    rgba k = task.px[y * w + (ox + x)];
                    if (!similar(c, k, opt.px_dist) || visited[y][ox+x]) {
                        ok = 0;
                        break;
                    }
                    mr.push_back(k.r);
                    mg.push_back(k.g);
                    mb.push_back(k.b);
                    ma.push_back(k.a);
                }
            }
            u32 oh = y - oy - (ok ? 0 : 1);

            sort(mr.begin(), mr.end());
            sort(mg.begin(), mg.end());
            sort(mb.begin(), mb.end());
            sort(ma.begin(), ma.end());
            u32 m = mr.size() / 2;
            rgba mc = { mr[m], mg[m], mb[m], ma[m] };

            u8 res = ops_fill_rect(state, osel, {ox, oy, ox + ow, oy + oh}, mc);
            if (!res) { clog << "! fill_rect borked" << endl; dump_state(state); return; }
            for (u32 y = 0; y < oh; ++y) {
                for (u32 x = 0; x < ow; ++x) {
                    visited[oy+y][ox+x] = 1;
                }
            }
        }
    }
}


static opt_state
optimize(void(*func)(prog_state&, const image&, const opt_state&), prog_state& in_state, const image& task) {
    const u32 W = in_state.root.w;
    rgba* pixels = (rgba*) malloc(sizeof(rgba) * W * W);
    image im = {W, W, pixels};

    auto object = [&im, &task, &func] (prog_state state, const opt_state& opt) {
        _Program = {};
        func(state, task, opt);
        image_fill_rect(im, state.root);
        u32 imdiff = image_dist(im, task);
        return _Program.cost + imdiff;
    };

    u32 best_score = u32_max;
    r64 cx_min = 0, cx = 10000;
    opt_state best = {cx};
    while (cx - cx_min > 0.5) {
        clog << "optimize " << cx << endl;
        r64 step = (cx - cx_min) / 4;
        r64 c1 = cx - 3 * step;
        r64 c2 = cx - 2 * step;
        r64 c3 = cx - 1 * step;

        u32 cost3 = object(in_state, {c3});
        clog << "    cost " << c3 << ": " << cost3 << endl;

        u32 cost2 = object(in_state, {c2});
        clog << "    cost " << c2 << ": " << cost2 << endl;

        u32 cost1 = object(in_state, {c1});
        clog << "    cost " << c1 << ": " << cost1 << endl;

        u32 m = min(cost1, min(cost2, cost3));

        opt_state opt = {cx};
        if (m == cost1) {
            cx = c2;
            best = {c1};
            best_score = cost1;
        }
        else if (m == cost3) {
            cx_min = c2;
            best = {c3};
            best_score = cost3;
        }
        else if (m == cost2) {
            cx_min = c1;
            cx = c3;
            best = {c2};
            best_score = cost2;
        }
    }
    clog << "best score " << best_score << " at dist=" << best.px_dist << endl;
    return best;
}


static void
problem(prog_state& state, const image& task) {
    auto opt = optimize(solve, state, task);
    _Program = {};
    solve(state, task, opt);
    program_print(_Program);
}


int
main(int argc, char const *argv[]) {
    std::ios_base::sync_with_stdio(false);
    constexpr const u32 W = 400;

    if (argc < 2) {
        puts("usage: solve task.png");
        return 0;
    }
    rgba* task_data;
    #ifdef STB_IMAGE_IMPLEMENTATION
    {
        i32 w, h, n;
        task_data = (rgba*) stbi_load(argv[1], &w, &h, &n, 0);
        if (!task_data) {
            printf("! could not read %s\n", argv[1]);
            return 1;
        }
        if (w != W || h != W) {
            printf("! unexpected image size %d,%d %s\n", w, h, argv[1]);
            return 1;
        }
        if (n != 4) {
            printf("! unexpected image planes %d %s\n", n, argv[1]);
            return 1;
        }
    }
    {
        FILE* fp = fopen("input.raw", "wb");
        if (!fp) { return 1; }
        fwrite(task_data, sizeof(rgba), W * W, fp);
    }
    #else
    {
        FILE* fp = fopen("input.raw", "rb");
        if (!fp) { return 1; }
        task_data = (rgba*) malloc(sizeof(rgba) * W * W);
        u32 n = fread(task_data, sizeof(rgba), W * W, fp);
        if (n != W * W) { return 1; }
    }
    #endif

    image task_image = {W, W, task_data};
    image_flip_vertically(task_image);

    static rgba pixels[W][W];

    image im = {W, W, (rgba*)pixels};
    block root = {ROOT_ID};
    root.w = im.w;
    root.h = im.h;
    root.children = {
        {.id=0, .x=0, .y=0, .w=root.w, .h=root.h, .px={im.w * im.h, {255,255,255,255}} },
    };
    prog_state state = {0, root};

    problem(state, task_image);

    image_fill_rect(im, state.root);
    image_flip_vertically(im);

    stbi_write_png("image.png", im.w, im.h, sizeof(rgba), pixels, im.w * sizeof(rgba));

    return 0;
}
