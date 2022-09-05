// c++ -std=c++20 -O2 -o solve solve.cpp
#include <algorithm>
#include <cstdint>
#include <deque>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
#include <unistd.h>
#define STB_IMAGE_IMPLEMENTATION
#include "stb/stb_image.h"
#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb/stb_image_write.h"

using std::abs;
using std::clog;
using std::cout;
using std::deque;
using std::endl;
using std::for_each;
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
typedef double r64;

static constexpr const u32 u32_max = std::numeric_limits<u32>::max();
static constexpr const r64 r64_inf = std::numeric_limits<r64>::infinity();


enum class app_mode { lite=0, base1=1, base2=2 };
enum class app_ops { cut_x, cut_y, cut_p, color, swap, merge, noop };

typedef struct {
    u32 line_cut, point_cut, color, swap, merge;
} cost_table;

static constexpr const
cost_table app_cost_table[] = {
    {7, 10, 5, 3, 1},
    {7, 10, 5, 3, 1},
    {2, 3, 5, 3, 1},
};
static constexpr const r64 alpha = 0.005;

static cost_table _Costs;


typedef union __attribute__((packed)) {
    struct {
        u8 r,g,b,a;
    };
    u32 value;
} rgba;


typedef struct {
    r64 r,g,b,a;
} fc;


typedef struct {
    u32 w, h;
    rgba* px;
} image;


typedef struct {
    u32 x, y, w, h;
    image* im;
} image_view;


typedef struct {
    u32 x, y;
} point;


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


bool operator == (const point& a, const point& b) {
    return a.x == b.x && a.y == b.y;
}

bool operator == (const ltrb& a, const ltrb& b) {
    return a.l == b.l && a.t == b.t && a.r == b.r && a.b == b.b;
}

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


std::ostream& operator << (std::ostream& so, const fc& px) {
    so << "[" << px.r << "," << px.g << "," << px.b << "," << px.a << "]";
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
eval_cost(u32 base_cost, const image_view& view) {
    r64 canvas = view.im->w * view.im->h;
    r64 block = view.w * view.h;
    return round(r64(base_cost) * canvas / block);
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
            clog << "! no path to " << x << "," << y << endl;
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
    program_append(_Program, so.str(), eval_cost(state, _Costs.color, *pr));
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
    program_append(_Program, so.str(), eval_cost(state, _Costs.line_cut, *pr));
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
    program_append(_Program, so.str(), eval_cost(state, _Costs.line_cut, *pr));
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
    program_append(_Program, so.str(), eval_cost(state, _Costs.point_cut, *pr));
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
    program_append(_Program, so.str(), eval_cost(state, _Costs.merge, big));
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
image_histogram(const image_view& view) {
    const u32 w = view.im->w;
    const auto* px = view.im->px;
    unordered_map<rgba, u32> histos;
    for (u32 y = 0; y < view.h; ++y) {
        for (u32 x = 0; x < view.w; ++x) {
            rgba c = px[(view.y + y) * w + (view.x + x)];
            histos[c] += 1;
        }
    }
    return histos;
}


static vector<rgba>
image_palette(const image_view& view) {
    auto histos = image_histogram(view);
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


static r64
image_dist(const image_view& a, const image_view& b) {
    if (a.w != b.w || a.h != b.h) { return u32_max; }
    const u32 aiw = a.im->w, biw = b.im->w;
    auto *da = a.im->px, *db = b.im->px;
    r64 diff = 0;
    for (u32 y = 0; y < a.h; ++y) {
        for (u32 x = 0; x < a.w; ++x) {
            auto& pa = da[(a.y + y) * aiw + (a.x + x)];
            auto& pb = db[(b.y + y) * biw + (b.x + x)];
            diff += pixel_dist(pa, pb);
        }
    }
    return diff;
}


static r64
image_dist(image& a, image& b) {
    image_view va = {.x=0, .y=0, .w=a.w, .h=a.h, .im=&a};
    image_view vb = {.x=0, .y=0, .w=b.w, .h=b.h, .im=&b};
    return image_dist(va, vb);
}


static r64
image_dist(const image_view& view, const rgba& q) {
    auto* px = view.im->px;
    u32 iw = view.im->w;
    r64 diff = 0;
    for (u32 y = 0; y < view.h; ++y) {
        for (u32 x = 0; x < view.w; ++x) {
            auto& p = px[(view.y + y) * iw + (view.x + x)];
            diff += pixel_dist(p, q);
        }
    }
    return diff;
}


static r64
image_dist(const image_view& view, const fc& q) {
    auto dist = [] (const rgba& p, const fc& q) -> r64 {
        r64 r = r64(p.r) - q.r;
        r64 g = r64(p.g) - q.g;
        r64 b = r64(p.b) - q.b;
        r64 a = r64(p.a) - q.a;
        return sqrt(r * r + g * g + b * b + a * a);
    };
    auto* px = view.im->px;
    u32 iw = view.im->w;
    r64 diff = 0;
    for (u32 y = 0; y < view.h; ++y) {
        for (u32 x = 0; x < view.w; ++x) {
            auto& p = px[(view.y + y) * iw + (view.x + x)];
            diff += dist(p, q);
        }
    }
    return diff;
}


static u8
similar(const rgba& p, const rgba& q, r64 w = 0) {
    return pixel_dist(p, q) <= w;
}


typedef struct {
    r64 px_dist;
} opt_state;


static rgba
image_sq_average(const image_view& view) {
    const u32 w = view.w;
    const u32 h = view.h;
    const u32 iw = view.im->w;
    r64 r,g,b,a, n = w * h;
    rgba* px = view.im->px;
    for (u32 y = 0; y < h; ++y) {
        for (u32 x = 0; x < w; ++x) {
            rgba c = px[(view.y + y) * iw + (view.x + x)];
            r += c.r * c.r;
            g += c.g * c.g;
            b += c.b * c.b;
            a += c.a * c.a;
        }
    }
    return {
        .r = u8(round(sqrt(r / n))),
        .g = u8(round(sqrt(g / n))),
        .b = u8(round(sqrt(b / n))),
        .a = u8(round(sqrt(a / n))),
    };
}


static r64
standard_deviation(const vector<fc>& v) {
    auto dist2 = [] (const fc& p, const fc& q) -> r64 {
        r64 r = q.r - p.r;
        r64 g = q.g - p.g;
        r64 b = q.b - p.b;
        r64 a = q.a - p.a;
        return (r * r + g * g + b * b + a * a);
    };
    fc mean = {};
    for (auto& x : v) {
        mean.r += x.r;
        mean.g += x.g;
        mean.b += x.b;
        mean.a += x.a;
    }
    mean.r /= v.size();
    mean.g /= v.size();
    mean.b /= v.size();
    mean.a /= v.size();
    r64 d = 0;
    for (auto& x : v) {
        d += dist2(x, mean);
    }
    return sqrt(d / v.size());
}


static rgba
image_nelder_mead(const image_view& im) {
    auto palette = image_palette(im);
    const u32 w = im.w;
    const u32 h = im.h;
    auto score = [&im] (const fc& p) -> r64 {
        return image_dist(im, p);
    };
    vector<fc> X(min(size_t(10), palette.size()));
    {
        for (u32 i = 0; i < X.size(); ++i) {
            rgba& c = palette[i];
            fc q;
            q.r = c.r;
            q.g = c.g;
            q.b = c.b;
            q.a = c.a;
            X[i] = q;
        }
    }
    for (u32 ii = 0; ; ++ii) {
        sort(X.begin(), X.end(), [&score] (const fc& p, const fc& q) {
            return score(p) < score(q);
        });

        auto s = standard_deviation(X);
        // clog << ii << ": " << s << ", " << X.front() << " " << X.back() << endl;
        if (s < 0.1) { break; }

        fc x0 = {};
        fc x1 = X[0];
        fc xn = X[X.size() - 2];
        fc xn1 = X[X.size() - 1];
        {
            for_each(X.begin(), X.end() - 1, [&x0] (const fc& a) {
                x0.r += a.r;
                x0.g += a.g;
                x0.b += a.b;
                x0.a += a.a;
            });
            x0.r /= X.size() - 1;
            x0.g /= X.size() - 1;
            x0.b /= X.size() - 1;
            x0.a /= X.size() - 1;
        }
        fc xr = {
            .r = x0.r * 2 - xn1.r,
            .g = x0.g * 2 - xn1.g,
            .b = x0.b * 2 - xn1.b,
            .a = x0.a * 2 - xn1.a,
        };
        r64 fr = score(xr);

        if (fr < score(xn) && fr >= score(x1)) {
            X.back() = xr;
            continue;
        }

        if (fr < score(x1)) {
            fc xe = {
                .r = xr.r * 2 - x0.r,
                .g = xr.g * 2 - x0.g,
                .b = xr.b * 2 - x0.b,
                .a = xr.a * 2 - x0.a,
            };
            if (score(xe) < fr) {
                X.back() = xe;
            }
            else {
                X.back() = xr;
            }
            continue;
        }

        if (fr < score(xn1)) {
            fc xc = {
                .r = (x0.r + xr.r) / 2,
                .g = (x0.g + xr.g) / 2,
                .b = (x0.b + xr.b) / 2,
                .a = (x0.a + xr.a) / 2,
            };
            if (score(xc) < fr) {
                X.back() = xc;
                continue;
            }
        }
        else {
            fc xc = {
                .r = (x0.r + xn1.r) / 2,
                .g = (x0.g + xn1.g) / 2,
                .b = (x0.b + xn1.b) / 2,
                .a = (x0.a + xn1.a) / 2,
            };
            if (score(xc) < score(xn1)) {
                X.back() = xc;
                continue;
            }
        }

        for (u32 i = 1; i < X.size(); ++i) {
            auto best = X[0];
            auto x = X[i];
            X[i] = {
                .r = (x.r + best.r) / 2,
                .g = (x.g + best.g) / 2,
                .b = (x.b + best.b) / 2,
                .a = (x.a + best.a) / 2,
            };
        }
    }
    auto best = X[0];
    rgba res = {
        .r = u8(round(best.r)),
        .g = u8(round(best.g)),
        .b = u8(round(best.b)),
        .a = u8(round(best.a)),
    };
    return res;
}


static rgba
smudge_color(const image_view& view) {
    return image_nelder_mead(view);
}


static rgba
smudge_color(prog_state& state, const id_path& sel, const image& task) {
    block* pr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { return {255,255,255,255}; }
    block& r = *pr;
    image_view chunk = {.x=r.x, .y=r.y, .w=r.w, .h=r.h, .im=(image*)&task};
    return smudge_color(chunk);
}


static u8
suggest_color(prog_state& state, const id_path& sel, const image& task, rgba* poc) {
    block* pr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { return 0; }
    block& r = *pr;
    // clog << "suggest_color " << sel << " " << r << endl;

    image block_image = {.w=r.w, .h=r.h, .px=(rgba*)&r.px[0]};
    image_view initial = {.x=0, .y=0, .w=r.w, .h=r.h, .im=&block_image};
    image_view chunk = {.x=r.x, .y=r.y, .w=r.w, .h=r.h, .im=(image*)&task};

    r64 cost1 = alpha * image_dist(initial, chunk);

    rgba bg = smudge_color(chunk);
    r64 cost2 = eval_cost(_Costs.color, chunk) + alpha * image_dist(chunk, bg);

    if (cost2 < cost1) {
        *poc = bg;
        return 1;
    }

    return 0;
}


typedef struct {
    app_ops cut_op;
    u32 cx, cy;
    u8 keep_bg;
} split;


static u8
suggest_split(prog_state& state, const image& task, const id_path& sel,
    const rgba& bg, split* pso) {
    // clog << "suggest_split " << sel << endl;
    block* parent;
    u8 res = select_leaf(state.root, sel, &parent);
    if (!res) { return 0; }
    {
        const u32 m = 2;
        block& r = *parent;
        if (r.w <= m && r.h <= m) { return 0; }
    }

    split s = {.cut_op=app_ops::noop, .keep_bg=1};

    typedef struct {
        u32 l, t, r, b;
        r64 cost;
        u8 empty;
        u8 paint;
    } rg;

    auto heur = [&task] (rg& r) -> r64 {
        image_view chunk = {.x=r.l, .y=r.t, .w=r.r-r.l, .h=r.b-r.t, .im=(image*)&task};
        rgba c = image_sq_average(chunk);
        return alpha * image_dist(chunk, c);
    };
    auto should_paint = [&task, &parent, &bg] (rg& r) -> u8 {
        block& p = *parent;
        image parent_image = {.w=p.w, .h=p.h, .px=&p.px[0]};
        image_view initial = {.x=(r.l-p.x), .y=(r.t-p.y), .w=r.r-r.l, .h=r.b-r.t, .im=(image*)&parent_image};
        #if 0
            image_view parent_full = {.x=p.x, .y=p.y, .w=p.w, .h=p.h, .im=(image*)&parent_image};
            r64 base_cost = eval_cost(_Costs.color, parent_full) + alpha * image_dist(initial, bg);
        #else
            r64 base_cost = alpha * image_dist(initial, bg);
        #endif
        image_view chunk = {.x=r.l, .y=r.t, .w=r.r-r.l, .h=r.b-r.t, .im=(image*)&task};
        // rgba c = smudge_color(chunk);
        rgba c = image_sq_average(chunk);
        r64 chunk_cost = eval_cost(_Costs.point_cut, chunk) + eval_cost(_Costs.color, chunk) + alpha * image_dist(chunk, c);
        return chunk_cost < base_cost;
    };

    rg pts[4];
    {
        block& r = *parent;
        pts[0] = {.l=r.x, .t=r.y, .r=r.x+1, .b=r.y+1};
        pts[1] = {.l=r.x+r.w-1, .t=r.y, .r=r.x+r.w, .b=r.y+1};
        pts[2] = {.l=r.x+r.w-1, .t=r.y+r.h-1, .r=r.x+r.w, .b=r.y+r.h};
        pts[3] = {.l=r.x, .t=r.y+r.h-1, .r=r.x+1, .b=r.y+r.h};
    }
    if (pts[1].l < pts[0].r) { pts[1].empty = 1; }
    if (pts[2].l < pts[3].r) { pts[2].empty = 1; }
    if (pts[2].t < pts[1].b) { pts[2].empty = 1; }
    if (pts[3].t < pts[0].b) { pts[3].empty = 1; }

    for (auto& q : pts) {
        q.cost = heur(q);
    }

    for (u8 done = 0; !done; ) {
        done = 1;

        u32 besti = u32_max;
        r64 best_cost = r64_inf;
        for (u32 i = 0; i < 4; ++i) {
            auto& q = pts[i];
            if (!q.empty && q.cost < best_cost) {
                best_cost = q.cost;
                besti = i;
            }
        }
        if (besti == u32_max) { break; }
        // clog << "  best " << besti << " " << best_cost << endl;

        auto& r = pts[besti];

        switch (besti) {
            case 0: {
                if (r.r - r.l < r.b - r.t || r.b >= pts[3].t) {
                    if (done && r.r < pts[1].l) {
                        r.r += 1;
                        done = 0;
                    }
                }
                if (done && r.b < pts[3].t) {
                    r.b += 1;
                    done = 0;
                }
                break;
            }
            case 1: {
                if (r.r - r.l < r.b - r.t || r.b >= pts[2].t) {
                    if (done && r.l > pts[0].r) {
                        r.l -= 1;
                        done = 0;
                    }
                }
                if (done && r.b < pts[2].t) {
                    r.b += 1;
                    done = 0;
                }
                break;
            }
            case 2: {
                if (r.r - r.l < r.b - r.t || r.t <= pts[1].b) {
                    if (done && r.l > pts[3].r) {
                        r.l -= 1;
                        done = 0;
                    }
                }
                if (done && r.t > pts[1].b) {
                    r.t -= 1;
                    done = 0;
                }
                break;
            }
            case 3: {
                if (r.r - r.l < r.b - r.t || r.t <= pts[0].b) {
                    if (done && r.r < pts[2].l) {
                        r.r += 1;
                        done = 0;
                    }
                }
                if (done && r.t > pts[0].b) {
                    r.t -= 1;
                    done = 0;
                }
                break;
            }
        }
        if (!done) {
            r.cost = heur(r);
        }
    }

#if 0
    clog << "pts:";
    for (u32 i = 0; i < 4; ++i) {
        clog << " [" << pts[i].l << "," << pts[i].t << "," << pts[i].r << "," << pts[i].b << "]";
    }
    clog << endl;
#endif

    s.cx = pts[1].l;
    s.cy = pts[2].t;

    if (!pts[1].empty) {
        if (!pts[3].empty) {
            s.cut_op = app_ops::cut_p;
        }
        else {
            s.cut_op = app_ops::cut_x;
        }
    }
    else {
        if (!pts[3].empty) {
            s.cut_op = app_ops::cut_y;
        }
        else {
            s.cut_op = app_ops::noop;
        }
    }

    if (s.cut_op != app_ops::noop) {
        s.keep_bg = 0;
        u8 blank = 1;
        for (u32 i = 0; i < 4; ++i) {
            auto& r = pts[i];
            if (!r.empty) {
                r.paint = should_paint(r);
                if (r.paint) {
                    blank = 0;
                }
                else {
                    s.keep_bg = 1;
                }
                break;
            }
        }
        if (blank) {
            s.cut_op = app_ops::noop;
        }
    }

    *pso = s;
    return s.cut_op != app_ops::noop;
}


static u8
ops_split(prog_state& state, const id_path& sel, app_ops cut, u32 cx, u32 cy) {
    block* pr;
    u8 res = select_leaf(state.root, sel, &pr);
    if (!res) { return 0; }
    block& r = *pr;
    // clog << "ops_split " << sel << " " << r << " cut:" << u32(cut) << " " << cx << "," << cy << endl;

    switch (cut) {
        case app_ops::cut_x: return op_cut_x(state, sel, cx);
        case app_ops::cut_y: return op_cut_y(state, sel, cy);
        case app_ops::cut_p: return op_cut_p(state, sel, cx, cy);
        default: return 0;
    }
}


static void
solve(prog_state& state, const image& task) {
    deque<id_path> fringe;

    auto init_walk = [&fringe] (block& r, id_path sel) -> void {
        auto init_walk = [&fringe] (const auto& init_walk, block& r, id_path sel) -> void {
            if (r.children.size() > 0) {
                for (auto& child : r.children) {
                    auto subsel = sel;
                    subsel.push_back(child.id);
                    init_walk(init_walk, child, subsel);
                }
            }
            else {
                fringe.push_back(sel);
            }
        };
        init_walk(init_walk, r, sel);
    };
    init_walk(state.root, {});

    while (fringe.size() > 0) {
        id_path sel = fringe.front();
        fringe.pop_front();
        // clog << "fringe pop " << sel << endl;

        block* pr;
        u8 res = select_at(state.root, sel, &pr);
        if (!res) { return; }

        if (pr->children.size() == 0) {
            block& r = *pr;
            image_view chunk = {.x=r.x, .y=r.y, .w=r.w, .h=r.h, .im=(image*)&task};
            rgba bg = smudge_color(chunk);
            u8 color_change = image_dist(chunk, bg) > 0;

            split spl;
            res = suggest_split(state, task, sel, bg, &spl);
            if (!res) {
                // clog << "no split" << endl;
                if (color_change) {
                    op_color(state, sel, bg);
                }
                continue;
            }

            if (spl.keep_bg && color_change) {
                op_color(state, sel, bg);
            }

            res = ops_split(state, sel, spl.cut_op, spl.cx, spl.cy);
            if (!res) { return; }
        }

        for (auto& child : pr->children) {
            auto subsel = sel;
            subsel.push_back(child.id);
            fringe.push_back(subsel);
        }
    }
}


int
main(int argc, char const *argv[]) {
    if (argc < 2) {
        puts("usage: solve task.png");
        return 0;
    }
    u8 expect_stdin = 0;
    if (argc > 2) {
        if (strcmp(argv[2], "-") == 0) {
            expect_stdin = 1;
        }
    }

    auto task_mode = app_mode::lite;

    u32 W=400, H=400, wh, res;
    rgba* source_data = nullptr;
    if (expect_stdin) {
        task_mode = app_mode::base1;
        res = read(STDIN_FILENO, &W, sizeof(W));
        if (!res) {
            puts("! missing initial at stdin");
            return 1;
        }
        read(STDIN_FILENO, &H, sizeof(H));
        read(STDIN_FILENO, &wh, sizeof(wh));
        if (wh) {
            task_mode = app_mode::base2;
            u8* buf = (u8*) malloc(sizeof(rgba) * W * H);
            if (!buf) { return 1; }

            for (u32 left = wh, off = 0; left > 0; ) {
                i32 n = read(STDIN_FILENO, &buf[off], left);
                if (n <= 0) { return 1; }
                off += n;
                left -= n;
            }

            #ifdef STB_IMAGE_IMPLEMENTATION
            i32 w, h, n;
            source_data = (rgba*) stbi_load_from_memory(buf, wh, &w, &h, &n, 0);
            if (!source_data) {
                clog << "! failed reading source image" << endl;
                return 1;
            }
            if (w != W || h != H || n != 4) {
                clog << "! invalid source size " << w << "," << h << endl;
                return 1;
            }
            #endif
        }
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
        if (w != W || h != H) {
            printf("! unexpected image size %d,%d %s\n", w, h, argv[1]);
            return 1;
        }
        if (n != 4) {
            printf("! unexpected image planes %d %s\n", n, argv[1]);
            return 1;
        }
    }
    // {
    //     FILE* fp = fopen("input.raw", "wb");
    //     if (!fp) { return 1; }
    //     fwrite(task_data, sizeof(rgba), W * H, fp);
    // }
    // #else
    // {
    //     FILE* fp = fopen("input.raw", "rb");
    //     if (!fp) { return 1; }
    //     task_data = (rgba*) malloc(sizeof(rgba) * W * H);
    //     u32 n = fread(task_data, sizeof(rgba), W * H, fp);
    //     if (n != W * H) { return 1; }
    // }
    #endif

    image task_image = {W, H, task_data};
    image task_source = {W, H, source_data};
    image_flip_vertically(task_image);
    if (task_source.px) {
        image_flip_vertically(task_source);
    }

    rgba* pixels = (rgba*) malloc(sizeof(rgba) * W * H);

    image im = {W, H, (rgba*)pixels};
    block root = {ROOT_ID};
    root.w = im.w;
    root.h = im.h;
    if (expect_stdin) {
        u32 nblocks;
        u32 res = read(STDIN_FILENO, &nblocks, sizeof(nblocks));
        if (res != sizeof(nblocks)) { return 1; }
        for (u32 bi = 0; bi < nblocks; ++bi) {
            u32 x, y, w, h, n, t, ct;
            id_path id;
            rgba c;
            read(STDIN_FILENO, &n, sizeof(n));
            for (u32 j = 0; j < n; ++j) {
                read(STDIN_FILENO, &t, sizeof(t));
                id.push_back(t);
            }
            read(STDIN_FILENO, &x, sizeof(x));
            read(STDIN_FILENO, &y, sizeof(y));
            read(STDIN_FILENO, &w, sizeof(w));
            read(STDIN_FILENO, &h, sizeof(h));
            read(STDIN_FILENO, &ct, sizeof(ct));
            vector<rgba> px(w * h);
            if (ct == 2) {
                u32 ox, oy;
                read(STDIN_FILENO, &ox, sizeof(ox));
                read(STDIN_FILENO, &oy, sizeof(oy));
                if (task_source.px) {
                    for (u32 a = 0; a < h; ++a) {
                        for (u32 b = 0; b < w; ++b) {
                            auto& c = task_source.px[(oy + a) + w + (ox + b)];
                            px[a * w + b] = c;
                        }
                    }
                }
            }
            else {
                read(STDIN_FILENO, &c, sizeof(c));
                for (u32 a = 0; a < h; ++a) {
                    for (u32 b = 0; b < w; ++b) {
                        px[a * w + b] = c;
                    }
                }
            }
            if (id.size() != 1) {
                clog << "! id: " << id << endl;
                return 1;
            }
            // clog << id << " [" << x << "," << y << "," << w << "," << h << "] " << c << endl;
            root.children.push_back({.id=id[0], .x=x, .y=y, .w=w, .h=h, .px=px});
        }
    }
    else {
        root.children = {
            {.id=0, .x=0, .y=0, .w=root.w, .h=root.h, .px={im.w * im.h, {255,255,255,255}} },
        };
    }
    prog_state state = {0, root};

    _Costs = app_cost_table[u32(task_mode)];

    _Program = {};
    solve(state, task_image);
    program_print(_Program);

    image_fill_rect(im, state.root);

    u32 imdiff = image_dist(im, task_image);
    u32 score = _Program.cost + round(alpha * imdiff);
    clog << "score: " << score << endl;

    image_flip_vertically(im);

    stbi_write_png("image.png", im.w, im.h, sizeof(rgba), pixels, im.w * sizeof(rgba));

    return 0;
}
