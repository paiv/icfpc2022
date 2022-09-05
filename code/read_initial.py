#!/usr/bin/env python
import json
import struct
import subprocess
import sys
from pathlib import Path


def http_download(url, path):
    import requests
    r = requests.get(url, stream=True)
    r.raise_for_status()
    with open(path, 'wb') as fp:
        for c in r.iter_content(1024):
            fp.write(c)
    with open(path, 'rb') as fp:
        return fp.read()


def dump_tree(root, level=0):
    s = ', '.join(f'{k}:{v!r}' for k,v in root.items() if k != 'blocks')
    print(' ' * level, s, file=sys.stderr)
    if (children := root.get('blocks')):
        for x in children:
            dump_tree(x, level+1)


def collect_blocks(root):
    if (children := root.get('blocks')):
        for x in children:
            yield from collect_blocks(x)
    else:
        i = root['blockId']
        i = list(map(int, i.split('.')))
        l,b = root['bottomLeft']
        r,t = root['topRight']
        c = root.get('color') or root.get('pngBottomLeftPoint')
        yield [i, l, b, r-l, t-b, c]


def api_pack(w, h, blocks, source):
    def ipack(x): return x.to_bytes(4, 'little')
    def pack4(v): return struct.pack('<4B', *v)
    def vpack(v): return ipack(len(v)) + b''.join(map(ipack, v))
    def pack_block(p):
        i,x,y,w,h,c = p
        t = len(c) == 2
        cref = vpack(c) if t else (ipack(0) + pack4(c))
        return vpack(i) + ipack(x) + ipack(y) + ipack(w) + ipack(h) + cref
    data = ipack(w)
    data += ipack(h)
    if source:
        data += ipack(len(source))
        data += source
    else:
        data += ipack(0)
    data += ipack(len(blocks))
    for b in blocks:
        data += pack_block(b)
    return data


def main(fn, prog, goal):
    fn = Path(fn)
    with open(fn) as fp:
        data = json.load(fp)

    dump_tree(data)

    initial_source = None
    if (src := data.get('sourcePngPNG')):
        dest = fn.parent / Path(src).name
        if dest.is_file():
            with open(dest, 'rb') as fp:
                initial_source = fp.read()
        else:
            initial_source = http_download(src, dest)

    w,h =  data['width'], data['height']
    blocks = list(collect_blocks(data))
    msg = api_pack(w, h, blocks, initial_source)
    p = subprocess.run([prog, goal, '-'], input=msg, stdout=None)
    p.check_returncode()


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('input', help='Task initial JSON')
    parser.add_argument('goal', help='Task goal PNG')
    parser.add_argument('-r', '--action', metavar='A', default='./solve', help='The program to feed')
    args = parser.parse_args()
    main(args.input, args.action, args.goal)
