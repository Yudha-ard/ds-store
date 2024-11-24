#!/usr/bin/env python
# -*- encoding: utf-8 -*-

import binascii
import bisect
import os
import struct
import plistlib
import struct
import mac_alias
import argparse
import os.path
import pprint
import re
import sys
from urllib.parse import urlparse
import queue
import threading
from io import BytesIO
import requests
from colorama import Fore, Back, Style

class BuddyError(Exception):
    pass

class Block:
    def __init__(self, allocator, offset, size):
        self._allocator = allocator
        self._offset = offset
        self._size = size
        self._value = bytearray(allocator.read(offset, size))
        self._pos = 0
        self._dirty = False

    def __len__(self):
        return self._size

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def close(self):
        if self._dirty:
            self.flush()

    def flush(self):
        if self._dirty:
            self._dirty = False
            self._allocator.write(self._offset, self._value)

    def invalidate(self):
        self._dirty = False

    def zero_fill(self):
        len = self._size - self._pos
        zeroes = b"\0" * len
        self._value[self._pos : self._size] = zeroes
        self._dirty = True

    def tell(self):
        return self._pos

    def seek(self, pos, whence=os.SEEK_SET):
        if whence == os.SEEK_CUR:
            pos += self._pos
        elif whence == os.SEEK_END:
            pos = self._size - pos

        if pos < 0 or pos > self._size:
            raise ValueError("Seek out of range in Block instance")
        
        self._pos = pos

    def read(self, size_or_format):
        if isinstance(size_or_format, (str, bytes)):
            size = struct.calcsize(size_or_format)
            fmt = size_or_format
        else:
            size = size_or_format
            fmt = None

        if self._size - self._pos < size:
            raise BuddyError("Unable to read %lu bytes in block" % size)

        data = self._value[self._pos : self._pos + size]
        self._pos += size

        if fmt is not None:
            if isinstance(data, bytearray):
                return struct.unpack_from(fmt, bytes(data))
            else:
                return struct.unpack(fmt, data)
        else:
            return data

    def write(self, data_or_format, *args):
        if len(args):
            data = struct.pack(data_or_format, *args)
        else:
            data = data_or_format

        if self._pos + len(data) > self._size:
            raise ValueError("Attempt to write past end of Block")

        self._value[self._pos : self._pos + len(data)] = data
        self._pos += len(data)

        self._dirty = True

    def insert(self, data_or_format, *args):
        if len(args):
            data = struct.pack(data_or_format, *args)
        else:
            data = data_or_format

        del self._value[-len(data) :]
        self._value[self._pos : self._pos] = data
        self._pos += len(data)

        self._dirty = True

    def delete(self, size):
        if self._pos + size > self._size:
            raise ValueError("Attempt to delete past end of Block")
        del self._value[self._pos : self._pos + size]
        self._value += b"\0" * size
        self._dirty = True

    def __str__(self):
        return binascii.b2a_hex(self._value)

class Allocator:
    def __init__(self, the_file):
        self._file = the_file
        self._dirty = False

        self._file.seek(0)

        (magic1, magic2, offset, size, offset2, self._unknown1) = self.read(
            -4, ">I4sIII16s"
        )

        if magic2 != b"Bud1" or magic1 != 1:
            raise BuddyError("Not a buddy file")

        if offset != offset2:
            raise BuddyError("Root addresses differ")

        self._root = Block(self, offset, size)

        count, self._unknown2 = self._root.read(">II")
        self._offsets = []
        c = (count + 255) & ~255
        while c:
            self._offsets += self._root.read(">256I")
            c -= 256
        self._offsets = self._offsets[:count]

        self._toc = {}
        count = self._root.read(">I")[0]
        for n in range(count):
            nlen = self._root.read("B")[0]
            name = bytes(self._root.read(nlen))
            value = self._root.read(">I")[0]
            self._toc[name] = value

        self._free = []
        for n in range(32):
            count = self._root.read(">I")
            self._free.append(list(self._root.read(">%uI" % count)))

    @classmethod
    def open(cls, file_or_name, mode="r+"):
        if isinstance(file_or_name, str):
            if "b" not in mode:
                mode = mode[:1] + "b" + mode[1:]
            f = open(file_or_name, mode)
        else:
            f = file_or_name

        if "w" in mode:
            f.truncate()

            header = struct.pack(
                b">I4sIII16s",
                1,
                b"Bud1",
                2048,
                1264,
                2048,
                b"\x00\x00\x10\x0c"
                b"\x00\x00\x00\x87"
                b"\x00\x00\x20\x0b"
                b"\x00\x00\x00\x00",
            )
            f.write(header)
            f.write(b"\0" * 2016)

            free_list = [struct.pack(b">5I", 0, 0, 0, 0, 0)]
            for n in range(5, 11):
                free_list.append(struct.pack(b">II", 1, 2**n))
            free_list.append(struct.pack(b">I", 0))
            for n in range(12, 31):
                free_list.append(struct.pack(b">II", 1, 2**n))
            free_list.append(struct.pack(b">I", 0))

            root = b"".join(
                [
                    struct.pack(b">III", 1, 0, 2048 | 5),
                    struct.pack(b">I", 0) * 255,
                    struct.pack(b">I", 0),
                ]
                + free_list
            )
            f.write(root)

        return Allocator(f)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def close(self):
        self.flush()
        self._file.close()

    def flush(self):
        if self._dirty:
            size = self._root_block_size()
            self.allocate(size, 0)
            with self.get_block(0) as rblk:
                self._write_root_block_into(rblk)

            addr = self._offsets[0]
            offset = addr & ~0x1F
            size = 1 << (addr & 0x1F)

            self._file.seek(0, os.SEEK_SET)
            self._file.write(
                struct.pack(
                    b">I4sIII16s", 1, b"Bud1", offset, size, offset, self._unknown1
                )
            )

            self._dirty = False

        self._file.flush()

    def read(self, offset, size_or_format):
        self._file.seek(offset + 4, os.SEEK_SET)

        if isinstance(size_or_format, str):
            size = struct.calcsize(size_or_format)
            fmt = size_or_format
        else:
            size = size_or_format
            fmt = None

        ret = self._file.read(size)
        if len(ret) < size:
            ret += b"\0" * (size - len(ret))

        if fmt is not None:
            if isinstance(ret, bytearray):
                ret = struct.unpack_from(fmt, bytes(ret))
            else:
                ret = struct.unpack(fmt, ret)

        return ret

    def write(self, offset, data_or_format, *args):
        self._file.seek(offset + 4, os.SEEK_SET)

        if len(args):
            data = struct.pack(data_or_format, *args)
        else:
            data = data_or_format

        self._file.write(data)

    def get_block(self, block):
        try:
            addr = self._offsets[block]
        except IndexError:
            return None

        offset = addr & ~0x1F
        size = 1 << (addr & 0x1F)

        return Block(self, offset, size)

    def _root_block_size(self):
        size = 8
        size += 4 * ((len(self._offsets) + 255) & ~255)

        size += 4
        size += sum([5 + len(s) for s in self._toc])
        size += sum([4 + 4 * len(fl) for fl in self._free])

        return size

    def _write_root_block_into(self, block):
        block.write(">II", len(self._offsets), self._unknown2)
        block.write(">%uI" % len(self._offsets), *self._offsets)
        extra = len(self._offsets) & 255
        if extra:
            block.write(b"\0\0\0\0" * (256 - extra))

        keys = list(self._toc.keys())
        keys.sort()

        block.write(">I", len(keys))
        for k in keys:
            block.write("B", len(k))
            block.write(k)
            block.write(">I", self._toc[k])

        for w, f in enumerate(self._free):
            block.write(">I", len(f))
            if len(f):
                block.write(">%uI" % len(f), *f)

    def _buddy(self, offset, width):
        f = self._free[width]
        b = offset ^ (1 << width)

        try:
            ndx = f.index(b)
        except ValueError:
            ndx = None

        return (f, b, ndx)

    def _release(self, offset, width):
        while True:
            f, b, ndx = self._buddy(offset, width)

            if ndx is None:
                break

            offset &= b
            width += 1
            del f[ndx]

        bisect.insort(f, offset)

        self._dirty = True

    def _alloc(self, width):
        w = width
        while not self._free[w]:
            w += 1
        while w > width:
            offset = self._free[w].pop(0)
            w -= 1
            self._free[w] = [offset, offset ^ (1 << w)]
        self._dirty = True
        return self._free[width].pop(0)

    def allocate(self, bytes, block=None):
        if block is None:
            try:
                block = self._offsets.index(0)
            except ValueError:
                block = len(self._offsets)
                self._offsets.append(0)

        width = max(bytes.bit_length(), 5)

        addr = self._offsets[block]
        offset = addr & ~0x1F

        if addr:
            blkwidth = addr & 0x1F
            if blkwidth == width:
                return block
            self._release(offset, width)
            self._offsets[block] = 0

        offset = self._alloc(width)
        self._offsets[block] = offset | width
        return block

    def release(self, block):
        addr = self._offsets[block]

        if addr:
            width = addr & 0x1F
            offset = addr & ~0x1F
            self._release(offset, width)

        if block == len(self._offsets):
            del self._offsets[block]
        else:
            self._offsets[block] = 0

    def __len__(self):
        return len(self._toc)

    def __getitem__(self, key):
        if not isinstance(key, str):
            raise TypeError("Keys must be of string type")
        if not isinstance(key, bytes):
            key = key.encode("latin_1")
        return self._toc[key]

    def __setitem__(self, key, value):
        if not isinstance(key, str):
            raise TypeError("Keys must be of string type")
        if not isinstance(key, bytes):
            key = key.encode("latin_1")
        self._toc[key] = value
        self._dirty = True

    def __delitem__(self, key):
        if not isinstance(key, str):
            raise TypeError("Keys must be of string type")
        if not isinstance(key, bytes):
            key = key.encode("latin_1")
        del self._toc[key]
        self._dirty = True

    def iterkeys(self):
        return self._toc.keys()

    def keys(self):
        return self._toc.keys()

    def __iter__(self):
        return self._toc.keys()

    def __contains__(self, key):
        return key in self._toc

class ILocCodec:
    @staticmethod
    def encode(point):
        return struct.pack(b">IIII", point[0], point[1], 0xFFFFFFFF, 0xFFFF0000)

    @staticmethod
    def decode(bytesData):
        if isinstance(bytesData, bytearray):
            x, y = struct.unpack_from(b">II", bytes(bytesData[:8]))
        else:
            x, y = struct.unpack(b">II", bytesData[:8])
        return (x, y)

class PlistCodec:
    @staticmethod
    def encode(plist):
        return plistlib.dumps(plist, fmt=plistlib.FMT_BINARY)

    @staticmethod
    def decode(bytes):
        return plistlib.loads(bytes)

class BookmarkCodec:
    @staticmethod
    def encode(bmk):
        return bmk.to_bytes()

    @staticmethod
    def decode(bytes):
        return mac_alias.Bookmark.from_bytes(bytes)

codecs = {
    b"Iloc": ILocCodec,
    b"bwsp": PlistCodec,
    b"lsvp": PlistCodec,
    b"lsvP": PlistCodec,
    b"icvp": PlistCodec,
    b"pBBk": BookmarkCodec,
}


class DSStoreEntry:

    def __init__(self, filename, code, typecode, value=None):
        if str != bytes and type(filename) == bytes:
            filename = filename.decode("utf-8")

        if not isinstance(code, bytes):
            code = code.encode("latin_1")

        self.filename = filename
        self.code = code
        self.type = typecode
        self.value = value

    @classmethod
    def read(cls, block):
        nlen = block.read(b">I")[0]
        filename = block.read(2 * nlen).decode("utf-16be")

        code, typecode = block.read(b">4s4s")

        if typecode == b"bool":
            value = block.read(b">?")[0]
        elif typecode == b"long" or typecode == b"shor":
            value = block.read(b">I")[0]
        elif typecode == b"blob":
            vlen = block.read(b">I")[0]
            value = block.read(vlen)

            codec = codecs.get(code, None)
            if codec:
                value = codec.decode(value)
                typecode = codec
        elif typecode == b"ustr":
            vlen = block.read(b">I")[0]
            value = block.read(2 * vlen).decode("utf-16be")
        elif typecode == b"type":
            value = block.read(b">4s")[0]
        elif typecode == b"comp" or typecode == b"dutc":
            value = block.read(b">Q")[0]
        else:
            raise ValueError('Unknown type code "%s"' % typecode)

        return DSStoreEntry(filename, code, typecode, value)

    def __lt__(self, other):
        if not isinstance(other, DSStoreEntry):
            raise TypeError("Can only compare against other DSStoreEntry objects")
        sfl = self.filename.lower()
        ofl = other.filename.lower()
        return sfl < ofl or (self.filename == other.filename and self.code < other.code)

    def __le__(self, other):
        if not isinstance(other, DSStoreEntry):
            raise TypeError("Can only compare against other DSStoreEntry objects")
        sfl = self.filename.lower()
        ofl = other.filename.lower()
        return sfl < ofl or (sfl == ofl and self.code <= other.code)

    def __eq__(self, other):
        if not isinstance(other, DSStoreEntry):
            raise TypeError("Can only compare against other DSStoreEntry objects")
        sfl = self.filename.lower()
        ofl = other.filename.lower()
        return sfl == ofl and self.code == other.code

    def __ne__(self, other):
        if not isinstance(other, DSStoreEntry):
            raise TypeError("Can only compare against other DSStoreEntry objects")
        sfl = self.filename.lower()
        ofl = other.filename.lower()
        return sfl != ofl or self.code != other.code

    def __gt__(self, other):
        if not isinstance(other, DSStoreEntry):
            raise TypeError("Can only compare against other DSStoreEntry objects")
        sfl = self.filename.lower()
        ofl = other.filename.lower()

        selfCode = self.code
        if str != bytes and type(selfCode) is bytes:
            selfCode = selfCode.decode("utf-8")
        otherCode = other.code
        if str != bytes and type(otherCode) is bytes:
            otherCode = otherCode.decode("utf-8")

        return sfl > ofl or (sfl == ofl and selfCode > otherCode)

    def __ge__(self, other):
        if not isinstance(other, DSStoreEntry):
            raise TypeError("Can only compare against other DSStoreEntry objects")
        sfl = self.filename.lower()
        ofl = other.filename.lower()
        return sfl > ofl or (sfl == ofl and self.code >= other.code)

    def byte_length(self):
        utf16 = self.filename.encode("utf-16be")
        length = 4 + len(utf16) + 8

        if isinstance(self.type, str):
            entry_type = self.type.encode("latin_1")
            value = self.value
        elif isinstance(self.type, (bytes, str)):
            entry_type = self.type
            value = self.value
        else:
            entry_type = b"blob"
            value = self.type.encode(self.value)

        if entry_type == b"bool":
            length += 1
        elif entry_type == b"long" or entry_type == b"shor":
            length += 4
        elif entry_type == b"blob":
            length += 4 + len(value)
        elif entry_type == b"ustr":
            utf16 = value.encode("utf-16be")
            length += 4 + len(utf16)
        elif entry_type == b"type":
            length += 4
        elif entry_type == b"comp" or entry_type == b"dutc":
            length += 8
        else:
            raise ValueError('Unknown type code "%s"' % entry_type)

        return length

    def write(self, block, insert=False):
        if insert:
            w = block.insert
        else:
            w = block.write

        if isinstance(self.type, str):
            entry_type = self.type.encode("latin_1")
            value = self.value
        elif isinstance(self.type, (bytes, str)):
            entry_type = self.type
            value = self.value
        else:
            entry_type = b"blob"
            value = self.type.encode(self.value)

        utf16 = self.filename.encode("utf-16be")
        w(b">I", len(utf16) // 2)
        w(utf16)
        w(b">4s4s", self.code, entry_type)

        if entry_type == b"bool":
            w(b">?", value)
        elif entry_type == b"long" or entry_type == b"shor":
            w(b">I", value)
        elif entry_type == b"blob":
            w(b">I", len(value))
            w(value)
        elif entry_type == b"ustr":
            utf16 = value.encode("utf-16be")
            w(b">I", len(utf16) // 2)
            w(utf16)
        elif entry_type == b"type":
            if isinstance(value, str):
                value = value.encode("latin_1")
            w(b">4s", value)
        elif entry_type == b"comp" or entry_type == b"dutc":
            w(b">Q", value)
        else:
            raise ValueError('Unknown type code "%s"' % entry_type)

    def __repr__(self):
        return f"<{self.filename} {self.code}>"


class DSStore:

    def __init__(self, store):
        self._store = store
        self._superblk = self._store["DSDB"]
        with self._get_block(self._superblk) as s:
            (
                self._rootnode,
                self._levels,
                self._records,
                self._nodes,
                self._page_size,
            ) = s.read(b">IIIII")
        self._min_usage = 2 * self._page_size // 3
        self._dirty = False

    @classmethod
    def open(cls, file_or_name, mode="r+", initial_entries=None):
        store = Allocator.open(file_or_name, mode)

        if mode == "w" or mode == "w+":
            superblk = store.allocate(20)
            store["DSDB"] = superblk
            page_size = 4096

            if not initial_entries:
                root = store.allocate(page_size)

                with store.get_block(root) as rootblk:
                    rootblk.zero_fill()

                with store.get_block(superblk) as s:
                    s.write(b">IIIII", root, 0, 0, 1, page_size)
            else:
                initial_entries = list(initial_entries)
                initial_entries.sort()
                current_level = initial_entries
                next_level = []
                levels = []
                ptr_size = 0
                node_count = 0
                while True:
                    total = 8
                    nodes = []
                    node = []
                    for e in current_level:
                        new_total = total + ptr_size + e.byte_length()
                        if new_total > page_size:
                            nodes.append(node)
                            next_level.append(e)
                            total = 8
                            node = []
                        else:
                            total = new_total
                            node.append(e)
                    if node:
                        nodes.append(node)

                    node_count += len(nodes)
                    levels.append(nodes)

                    if len(nodes) == 1:
                        break

                    current_level = next_level
                    next_level = []
                    ptr_size = 4

                ptrs = [store.allocate(page_size) for n in range(node_count)]

                pointers = []
                prev_pointers = None
                for level in levels:
                    ppndx = 0
                    lptrs = ptrs[-len(level) :]
                    del ptrs[-len(level) :]
                    for node in level:
                        ndx = lptrs.pop(0)
                        if prev_pointers is None:
                            with store.get_block(ndx) as block:
                                block.write(b">II", 0, len(node))
                                for e in node:
                                    e.write(block)
                        else:
                            next_node = prev_pointers[ppndx + len(node)]
                            node_ptrs = prev_pointers[ppndx : ppndx + len(node)]

                            with store.get_block(ndx) as block:
                                block.write(b">II", next_node, len(node))
                                for ptr, e in zip(node_ptrs, node):
                                    block.write(b">I", ptr)
                                    e.write(block)

                        pointers.append(ndx)
                    prev_pointers = pointers
                    pointers = []

                root = prev_pointers[0]

                with store.get_block(superblk) as s:
                    s.write(
                        b">IIIII",
                        root,
                        len(levels),
                        len(initial_entries),
                        node_count,
                        page_size,
                    )

        return DSStore(store)

    def _get_block(self, number):
        return self._store.get_block(number)

    def flush(self):
        if self._dirty:
            self._dirty = False

            with self._get_block(self._superblk) as s:
                s.write(
                    b">IIIII",
                    self._rootnode,
                    self._levels,
                    self._records,
                    self._nodes,
                    self._page_size,
                )
        self._store.flush()

    def close(self):
        self.flush()
        self._store.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def _traverse(self, node):
        if node is None:
            node = self._rootnode
        with self._get_block(node) as block:
            next_node, count = block.read(b">II")
            if next_node:
                for n in range(count):
                    ptr = block.read(b">I")[0]
                    for e in self._traverse(ptr):
                        yield e
                    e = DSStoreEntry.read(block)
                    yield e
                for e in self._traverse(next_node):
                    yield e
            else:
                for n in range(count):
                    e = DSStoreEntry.read(block)
                    yield e

    def _dump_node(self, node):
        with self._get_block(node) as block:
            next_node, count = block.read(b">II")
            print("next: %u\ncount: %u\n" % (next_node, count))
            for n in range(count):
                if next_node:
                    ptr = block.read(b">I")[0]
                    print("%8u " % ptr, end=" ")
                else:
                    print("         ", end=" ")
                e = DSStoreEntry.read(block)
                print(e, " (%u)" % e.byte_length())
            print("used: %u" % block.tell())

    def _dump_super(self):
        print(
            "root: %u\nlevels: %u\nrecords: %u\nnodes: %u\npage-size: %u"
            % (
                self._rootnode,
                self._levels,
                self._records,
                self._nodes,
                self._page_size,
            )
        )

    def _split2(self, blocks, entries, pointers, before, internal):
        left_block = blocks[0]
        right_block = blocks[1]

        count = len(entries)

        best_split = None
        best_diff = None
        total = before[count]

        if 8 + total <= self._page_size:
            best_split = count
        else:
            for n in range(1, count - 1):
                left_size = 8 + before[n]
                right_size = 8 + total - before[n + 1]

                if left_size > self._page_size:
                    break
                if right_size > self._page_size:
                    continue

                diff = abs(left_size - right_size)

                if best_split is None or diff < best_diff:
                    best_split = n
                    best_diff = diff

        if best_split is None:
            return None

        left_block.seek(0)
        if internal:
            next_node = pointers[best_split]
        else:
            next_node = 0
        left_block.write(b">II", next_node, best_split)

        for n in range(best_split):
            if internal:
                left_block.write(b">I", pointers[n])
            entries[n].write(left_block)

        left_block.zero_fill()

        if best_split == count:
            return []

        right_block.seek(0)
        if internal:
            next_node = pointers[count]
        else:
            next_node = 0
        right_block.write(b">II", next_node, count - best_split - 1)

        for n in range(best_split + 1, count):
            if internal:
                right_block.write(b">I", pointers[n])
            entries[n].write(right_block)

        right_block.zero_fill()

        pivot = entries[best_split]

        return [pivot]

    def _split(self, node, entry, right_ptr=0):
        self._nodes += 1
        self._dirty = True
        new_right = self._store.allocate(self._page_size)
        with self._get_block(node) as block, self._get_block(new_right) as right_block:

            entry_size = entry.byte_length()
            next_node, count = block.read(b">II")
            if next_node:
                entry_size += 4
            pointers = []
            entries = []
            before = []
            total = 0
            for n in range(count):
                pos = block.tell()
                if next_node:
                    ptr = block.read(b">I")[0]
                    pointers.append(ptr)
                e = DSStoreEntry.read(block)
                if e > entry:
                    # ?? entry_pos = n
                    entries.append(entry)
                    pointers.append(right_ptr)
                    before.append(total)
                    total += entry_size
                entries.append(e)
                before.append(total)
                total += block.tell() - pos
            before.append(total)
            if next_node:
                pointers.append(next_node)

            pivot = self._split2(
                [block, right_block], entries, pointers, before, bool(next_node)
            )[0]

            self._records += 1
            self._nodes += 1
            self._dirty = True

        return (pivot, new_right)

    def _new_root(self, left, pivot, right):
        new_root = self._store.allocate(self._page_size)
        with self._get_block(new_root) as block:
            block.write(b">III", right, 1, left)
            pivot.write(block)
        self._rootnode = new_root
        self._levels += 1
        self._nodes += 1
        self._dirty = True

    def _insert_inner(self, path, node, entry, right_ptr):
        with self._get_block(node) as block:
            next_node, count = block.read(b">II")
            insert_pos = None
            insert_ndx = None
            n = 0
            while n < count:
                pos = block.tell()
                ptr = block.read(b">I")[0]
                e = DSStoreEntry.read(block)
                if e == entry:
                    if n == count - 1:
                        right_ptr = next_node
                        next_node = ptr
                        block.seek(pos)
                    else:
                        right_ptr = block.read(b">I")[0]
                        block.seek(pos + 4)
                    insert_pos = pos
                    insert_ndx = n
                    block.delete(e.byte_length() + 4)
                    count -= 1
                    self._records += 1
                    self._dirty = True
                    continue
                elif insert_pos is None and e > entry:
                    insert_pos = pos
                    insert_ndx = n
                n += 1
            if insert_pos is None:
                insert_pos = block.tell()
                insert_ndx = count
            remaining = self._page_size - block.tell()

            if remaining < entry.byte_length() + 4:
                pivot, new_right = self._split(node, entry, right_ptr)
                if path:
                    self._insert_inner(path[:-1], path[-1], pivot, new_right)
                else:
                    self._new_root(node, pivot, new_right)
            else:
                if insert_ndx == count:
                    block.seek(insert_pos)
                    block.write(b">I", next_node)
                    entry.write(block)
                    next_node = right_ptr
                else:
                    block.seek(insert_pos + 4)
                    entry.write(block, True)
                    block.insert(">I", right_ptr)
                block.seek(0)
                count += 1
                block.write(b">II", next_node, count)
                self._records += 1
                self._dirty = True

    def _insert_leaf(self, path, node, entry):
        with self._get_block(node) as block:
            next_node, count = block.read(b">II")
            insert_pos = None
            n = 0
            while n < count:
                pos = block.tell()
                e = DSStoreEntry.read(block)
                if e == entry:
                    insert_pos = pos
                    block.seek(pos)
                    block.delete(e.byte_length())
                    count -= 1
                    self._records += 1
                    self._dirty = True
                    continue
                elif insert_pos is None and e > entry:
                    insert_pos = pos
                n += 1
            if insert_pos is None:
                insert_pos = block.tell()
            remaining = self._page_size - block.tell()

            if remaining < entry.byte_length():
                pivot, new_right = self._split(node, entry)
                if path:
                    self._insert_inner(path[:-1], path[-1], pivot, new_right)
                else:
                    self._new_root(node, pivot, new_right)
            else:
                block.seek(insert_pos)
                entry.write(block, True)
                block.seek(0)
                count += 1
                block.write(b">II", next_node, count)
                self._records += 1
                self._dirty = True

    def insert(self, entry):
        path = []
        node = self._rootnode
        while True:
            with self._get_block(node) as block:
                next_node, count = block.read(b">II")
                if next_node:
                    for n in range(count):
                        ptr = block.read(b">I")[0]
                        e = DSStoreEntry.read(block)
                        if entry < e:
                            next_node = ptr
                            break
                        elif entry == e:
                            self._insert_inner(path, node, entry, None)
                            return
                    path.append(node)
                    node = next_node
                else:
                    self._insert_leaf(path, node, entry)
                    return

    def _block_usage(self, node):
        with self._get_block(node) as block:
            next_node, count = block.read(b">II")

            for n in range(count):
                if next_node:
                    block.read(b">I")[0]
                DSStoreEntry.read(block)

            used = block.tell()

        return (count, used)

    def _split3(self, blocks, entries, pointers, before, internal):
        count = len(entries)

        best_split = None
        best_diff = None
        total = before[count]
        for n in range(1, count - 3):
            left_size = 8 + before[n]
            remaining = 16 + total - before[n + 1]

            if left_size > self._page_size:
                break
            if remaining > 2 * self._page_size:
                continue

            for m in range(n + 2, count - 1):
                mid_size = 8 + before[m] - before[n + 1]
                right_size = 8 + total - before[m + 1]

                if mid_size > self._page_size:
                    break
                if right_size > self._page_size:
                    continue

                diff = abs(left_size - mid_size) * abs(right_size - mid_size)

                if best_split is None or diff < best_diff:
                    best_split = (n, m, count)
                    best_diff = diff

        if best_split is None:
            return None

        prev_split = -1
        for block, split in zip(blocks, best_split):
            block.seek(0)
            if internal:
                next_node = pointers[split]
            else:
                next_node = 0
            block.write(b">II", next_node, split)

            for n in range(prev_split + 1, split):
                if internal:
                    block.write(b">I", pointers[n])
                entries[n].write(block)

            block.zero_fill()

            prev_split = split

        return (entries[best_split[0]], entries[best_split[1]])

    def _extract(self, blocks, pivots):
        pointers = []
        entries = []
        before = []
        total = 0
        ppivots = pivots + [None]
        for b, p in zip(blocks, ppivots):
            b.seek(0)
            next_node, count = b.read(b">II")
            for n in range(count):
                pos = b.tell()
                if next_node:
                    ptr = b.read(b">I")[0]
                    pointers.append(ptr)
                e = DSStoreEntry.read(b)
                entries.append(e)
                before.append(total)
                total += b.tell() - pos
            if next_node:
                pointers.append(next_node)
            if p:
                entries.append(p)
                before.append(total)
                total += p.byte_length()
                if next_node:
                    total += 4
        before.append(total)

        return (entries, pointers, before)

    def _rebalance(self, path, node):
        if not path:
            return

        with self._get_block(node) as block:
            next_node, count = block.read(b">II")

            with self._get_block(path[-1]) as parent:
                parent_next, parent_count = parent.read(b">II")
                left_pos = None
                left_node = None
                left_pivot = None
                node_pos = None
                right_pos = None
                right_node = None
                right_pivot = None
                prev_e = prev_ptr = prev_pos = None
                for n in range(parent_count):
                    pos = parent.tell()
                    ptr = parent.read(b">I")[0]
                    e = DSStoreEntry.read(parent)

                    if ptr == node:
                        node_pos = pos
                        right_pivot = e
                        left_pos = prev_pos
                        left_pivot = prev_e
                        left_node = prev_ptr
                    elif prev_ptr == node:
                        right_node = ptr
                        right_pos = pos
                        break

                    prev_e = e
                    prev_ptr = ptr
                    prev_pos = pos

                if parent_next == node:
                    node_pos = parent.tell()
                    left_pos = prev_pos
                    left_pivot = prev_e
                    left_node = prev_ptr
                elif right_node is None:
                    right_node = parent_next
                    right_pos = parent.tell()

                _ = parent.tell()

            if left_node and right_node:
                with self._get_block(left_node) as left, self._get_block(
                    right_node
                ) as right:
                    blocks = [left, block, right]
                    pivots = [left_pivot, right_pivot]

                    entries, pointers, before = self._extract(blocks, pivots)

                    pivots = self._split2(
                        blocks, entries, pointers, before, bool(next_node)
                    )
                    if pivots is None:
                        ptrs = [left_node, node, right_node]
                        pivots = self._split3(
                            blocks, entries, pointers, before, bool(next_node)
                        )
                    else:
                        if pivots:
                            ptrs = [left_node, node]
                        else:
                            ptrs = [left_node]
                            self._store.release(node)
                            self._nodes -= 1
                            node = left_node
                        self._store.release(right_node)
                        self._nodes -= 1
                        self._dirty = True

                    with self._get_block(path[-1]) as parent:
                        if right_node == parent_next:
                            parent.seek(left_pos)
                            parent.delete(right_pos - left_pos)
                            parent_next = left_node
                        else:
                            parent.seek(left_pos + 4)
                            parent.delete(right_pos - left_pos)
                        parent.seek(0)
                        parent_count -= 2
                        parent.write(b">II", parent_next, parent_count)
                        self._records -= 2

                    for e, rp in zip(pivots, ptrs[1:]):
                        self._insert_inner(path[:-1], path[-1], e, rp)
            elif left_node:
                with self._get_block(left_node) as left:
                    blocks = [left, block]
                    pivots = [left_pivot]

                    entries, pointers, before = self._extract(blocks, pivots)

                    pivots = self._split2(
                        blocks, entries, pointers, before, bool(next_node)
                    )

                    with self._get_block(path[-1]) as parent:
                        if node == parent_next:
                            parent.seek(left_pos)
                            parent.delete(node_pos - left_pos)
                            parent_next = left_node
                        else:
                            parent.seek(left_pos + 4)
                            parent.delete(node_pos - left_pos)
                        parent.seek(0)
                        parent_count -= 1
                        parent.write(b">II", parent_next, parent_count)
                        self._records -= 1

                    if pivots:
                        self._insert_inner(path[:-1], path[-1], pivots[0], node)
            elif right_node:
                with self._get_block(right_node) as right:
                    blocks = [block, right]
                    pivots = [right_pivot]

                    entries, pointers, before = self._extract(blocks, pivots)

                    pivots = self._split2(
                        blocks, entries, pointers, before, bool(next_node)
                    )

                    with self._get_block(path[-1]) as parent:
                        if right_node == parent_next:
                            parent.seek(pos)
                            parent.delete(right_pos - node_pos)
                            parent_next = node
                        else:
                            parent.seek(pos + 4)
                            parent.delete(right_pos - node_pos)
                        parent.seek(0)
                        parent_count -= 1
                        parent.write(b">II", parent_next, parent_count)
                        self._records -= 1

                    if pivots:
                        self._insert_inner(path[:-1], path[-1], pivots[0], right_node)

        if not path and not parent_count:
            self._store.release(path[-1])
            self._nodes -= 1
            self._dirty = True
            self._rootnode = node
        else:
            count, used = self._block_usage(path[-1])

            if used < self._page_size // 2:
                self._rebalance(path[:-1], path[-1])

    def _delete_leaf(self, node, filename_lc, code):
        found = False

        with self._get_block(node) as block:
            next_node, count = block.read(b">II")

            for n in range(count):
                pos = block.tell()
                e = DSStoreEntry.read(block)
                if e.filename.lower() == filename_lc and (
                    code is None or e.code == code
                ):
                    block.seek(pos)
                    block.delete(e.byte_length())
                    found = True

                    count -= 1

                    self._records -= 1
                    self._dirty = True

            if found:
                used = block.tell()

                block.seek(0)
                block.write(b">II", next_node, count)

                return used < self._page_size // 2
            else:
                return False

    def _take_largest(self, path, node):
        path = list(path)
        rebalance = None
        while True:
            with self._get_block(node) as block:
                next_node, count = block.read(b">II")

                if next_node:
                    path.append(node)
                    node = next_node
                    continue

                for n in range(count):
                    pos = block.tell()
                    e = DSStoreEntry.read(block)

                count -= 1
                block.seek(0)
                block.write(b">II", next_node, count)

                if pos < self._page_size // 2:
                    rebalance = (path, node)
                break

        return rebalance, e

    def _delete_inner(self, path, node, filename_lc, code):
        rebalance = False

        with self._get_block(node) as block:
            next_node, count = block.read(b">II")

            for n in range(count):
                pos = block.tell()
                ptr = block.read(b">I")[0]
                e = DSStoreEntry.read(block)
                if e.filename.lower() == filename_lc and (
                    code is None or e.code == code
                ):
                    rebalance, largest = self._take_largest(path, ptr)

                    if n == count - 1:
                        right_ptr = next_node
                        next_node = ptr
                        block.seek(pos)
                    else:
                        right_ptr = block.read(b">I")[0]
                        block.seek(pos + 4)

                    block.delete(e.byte_length() + 4)

                    count -= 1
                    block.seek(0)
                    block.write(b">II", next_node, count)

                    self._records -= 1
                    self._dirty = True

                    break

        self._insert_inner(path, node, largest, right_ptr)

        if rebalance:
            self._rebalance(rebalance[0], rebalance[1])
            return True
        return False

    def delete(self, filename, code):
        if isinstance(filename, DSStoreEntry):
            code = filename.code
            filename = filename.filename

        if code is None:
            # TODO: Fix this so we can do bulk deletes
            raise ValueError("You must delete items individually.  Sorry")

        filename_lc = filename.lower()
        path = []
        node = self._rootnode
        while True:
            with self._get_block(node) as block:
                next_node, count = block.read(b">II")
                if next_node:
                    for n in range(count):
                        ptr = block.read(b">I")[0]
                        e = DSStoreEntry.read(block)
                        e_lc = e.filename.lower()
                        if filename_lc < e_lc or (
                            filename_lc == e_lc and code < e.code
                        ):
                            next_node = ptr
                            break
                        elif filename_lc == e_lc and code == e.code:
                            self._delete_inner(path, node, filename_lc, code)
                            return
                    path.append(node)
                    node = next_node
                else:
                    if self._delete_leaf(node, filename_lc, code):
                        self._rebalance(path, node)
                    return

    def _find(self, node, filename_lc, code=None):
        if code is not None and not isinstance(code, bytes):
            code = code.encode("latin_1")
        with self._get_block(node) as block:
            next_node, count = block.read(b">II")
            if next_node:
                for n in range(count):
                    ptr = block.read(b">I")[0]
                    e = DSStoreEntry.read(block)
                    if filename_lc < e.filename.lower():
                        for e in self._find(ptr, filename_lc, code):
                            yield e
                        return
                    elif filename_lc == e.filename.lower():
                        if code is None or (code and code < e.code):
                            for e in self._find(ptr, filename_lc, code):
                                yield e
                        if code is None or code == e.code:
                            yield e
                        elif code < e.code:
                            return
                for e in self._find(next_node, filename_lc, code):
                    yield e
            else:
                for n in range(count):
                    e = DSStoreEntry.read(block)
                    if filename_lc == e.filename.lower():
                        if code is None or code == e.code:
                            yield e
                        elif code < e.code:
                            return

    def find(self, filename, code=None):
        if isinstance(filename, DSStoreEntry):
            code = filename.code
            filename = filename.filename

        filename_lc = filename.lower()

        return self._find(self._rootnode, filename_lc, code)

    def __len__(self):
        return self._records

    def __iter__(self):
        return self._traverse(self._rootnode)

    class Partial:

        def __init__(self, store, filename):
            self._store = store
            self._filename = filename

        def __getitem__(self, code):
            if code is None:
                raise KeyError("no such key - [%s][None]" % self._filename)

            if not isinstance(code, bytes):
                code = code.encode("latin_1")

            try:
                item = next(self._store.find(self._filename, code))
            except StopIteration:
                raise KeyError(f"no such key - [{self._filename}][{code}]")

            if not isinstance(item.type, (bytes, str)):
                return item.value

            return (item.type, item.value)

        def __setitem__(self, code, value):
            if code is None:
                raise KeyError("bad key - [%s][None]" % self._filename)

            if not isinstance(code, bytes):
                code = code.encode("latin_1")

            codec = codecs.get(code, None)
            if codec:
                entry_type = codec
                entry_value = value
            else:
                entry_type = value[0]
                entry_value = value[1]

            self._store.insert(
                DSStoreEntry(self._filename, code, entry_type, entry_value)
            )

        def __delitem__(self, code):
            if code is None:
                raise KeyError("no such key - [%s][None]" % self._filename)

            self._store.delete(self._filename, code)

        def __iter__(self):
            yield from self._store.find(self._filename)

    def __getitem__(self, filename):
        return self.Partial(self, filename)

_not_printable_re = re.compile(rb"[\x00-\x1f\x7f-\x9f]")


def usage():
    print(main.__doc__)
    sys.exit(0)


def chunks(iterable, length):
    for i in range(0, len(iterable), length):
        yield i, iterable[i : i + length]


def pretty(value):
    if isinstance(value, dict):
        return f"{{\n {pprint.pformat(value, indent=4)[1:-1]}\n}}"
    elif isinstance(value, bytearray):
        lines = ["["]
        for offset, chunk in chunks(value, 16):
            printable_chunk = _not_printable_re.sub(b".", chunk).decode("latin-1")
            hex_line = " ".join([f"{b:02x}" for b in chunk])
            line = f"  {offset:08x}  {hex_line:<47s}  {printable_chunk}"
            lines.append(line)
        lines.append("]")
        return "\n".join(lines)
    elif isinstance(value, bytes):
        return value.decode("latin-1")
    else:
        return value


def main(argv):

    parser = argparse.ArgumentParser(description=main.__doc__)
    parser.add_argument("paths", nargs="*")
    args = parser.parse_args(argv)

    if len(args.paths) == 0:
        args.paths = ["."]

    failed = False
    for path in args.paths:
        if os.path.isdir(path):
            path = os.path.join(path, ".DS_Store")

        if not os.path.exists(path) or not os.path.isfile(path):
            print(f"ds_store: {path} not found", file=sys.stderr)
            failed = True
            continue

        try:
            with DSStore.open(path, "r") as d:
                print(path)
                print("")

                max_name_len = 0
                for entry in d:
                    name_len = len(entry.filename)
                    if name_len > max_name_len:
                        max_name_len = name_len

                for entry in d:
                    print(
                        "{:<{width}} {} {}".format(
                            entry.filename,
                            entry.code.decode("latin-1"),
                            pretty(entry.value),
                            width=max_name_len,
                        )
                    )
                print("")
        except BuddyError as e:
            print(f"ds_store: {path}: {e}")
            failed = True

    if failed:
        sys.exit(1)

class scanner(object):
    def __init__(self, start_url):
        self.queue = queue.Queue()
        self.queue.put(start_url)
        self.processed_url = set()
        self.lock = threading.Lock()
        self.working_thread = 0
        self.dest_dir = os.path.abspath('.')

    def is_valid_name(self, entry_name):
        if entry_name.find('..') >= 0 or \
                entry_name.startswith('/') or \
                entry_name.startswith('\\') or \
                not os.path.abspath(entry_name).startswith(self.dest_dir):
            try:
                print('\033[31m[ERROR] Invalid entry name: %s\033[0m' % entry_name)
            except Exception as e:
                pass
            return False
        return True

    def process(self):
        while True:
            try:
                url = self.queue.get(timeout=2.0)
                self.lock.acquire()
                self.working_thread += 1
                self.lock.release()
            except Exception as e:
                if self.working_thread == 0:
                    break
                else:
                    continue
            try:
                if url in self.processed_url:
                    continue
                else:
                    self.processed_url.add(url)
                
                base_url = url.rstrip('.DS_Store')

                if not url.lower().startswith('http'):
                    url = 'http://%s' % url
                schema, netloc, path, _, _, _ = urlparse(url, 'http')

                try:
                    response = requests.get(url, allow_redirects=False)
                except Exception as e:
                    self.lock.acquire()
                    print('\033[31m[ERROR] %s\033[0m' % str(e))
                    self.lock.release()
                    continue

                if response.status_code == 200:
                    folder_name = netloc.replace(':', '_') + '/'.join(path.split('/')[:-1])
                    if not os.path.exists(folder_name):
                        os.makedirs(folder_name)
                    with open(netloc.replace(':', '_') + path, 'wb') as outFile:
                        self.lock.acquire()
                        print('\033[32m[%s] %s\033[0m' % (response.status_code, url))
                        self.lock.release()
                        outFile.write(response.content)
                    if url.endswith('.DS_Store'):
                        ds_store_file = BytesIO()
                        ds_store_file.write(response.content)
                        d = DSStore.open(ds_store_file)

                        dirs_files = set()
                        for x in d._traverse(None):
                            if self.is_valid_name(x.filename):
                                dirs_files.add(x.filename)
                        for name in dirs_files:
                            if name != '.':
                                self.queue.put(base_url + name)
                                if len(name) <= 4 or name[-4] != '.':
                                    self.queue.put(base_url + name + '/.DS_Store')
                        d.close()
            except Exception as e:
                self.lock.acquire()
                print('\033[31m[ERROR] %s\033[0m' % str(e))
                self.lock.release()
            finally:
                self.working_thread -= 1

    def scan(self):
        all_threads = []
        for i in range(10):
            t = threading.Thread(target=self.process)
            all_threads.append(t)
            t.start()

if __name__ == '__main__':
    if len(sys.argv) == 1:
        print(
        f"""
        
           __   ___     ___ __        {Fore.YELLOW}v.1.0{Fore.GREEN}              
          / _ \/ __/___/ __/ /____  _______ 
         / // /\ \/___/\ \/ __/ _ \/ __/ -_)
        {Fore.WHITE}/____/___/   /___/\__/\___/_/  \__/ {Fore.WHITE}
            
        {Fore.RED}DS-Store{Fore.WHITE} - {Fore.YELLOW}.DS-Store file parsher.{Fore.WHITE}
        @Yudha_Ard (https://github.com/yudha-ard)
            
        usage : {Fore.YELLOW}main.py {Fore.GREEN}https://www.site.com/.DS_Store{Fore.WHITE}
        """)

        sys.exit(0)
    s = scanner(sys.argv[1])
    s.scan()
