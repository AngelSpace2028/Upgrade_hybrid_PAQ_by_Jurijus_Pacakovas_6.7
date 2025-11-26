import os
import sys
import math
import struct
import array
import random
import heapq
import binascii
import logging
import hashlib
from datetime import datetime
from enum import Enum
from typing import List, Dict, Tuple, Optional

# === Optional: Qiskit (quantum-inspired, not required) ===
qiskit = None
try:
    import qiskit
except ImportError:
    logging.warning("qiskit not available, skipping quantum circuit definition")

# === Optional: PAQ9a binding (pip install paq) ===
try:
    import paq
except ImportError:
    logging.error("paq module not found. Install with: pip install paq")
    sys.exit(1)

import zipfile
import urllib.request

# === Download Dictionaries ===
def download_dictionaries():
    zip_url = "https://drive.google.com/uc?id=1cPGyuwtozYjFVZd2wBmJvKWa7Xoy0Y-A"
    output_zip = "dictionaries.zip"
    if os.path.exists(output_zip):
        logging.info("Dictionary zip already downloaded.")
        return
    try:
        urllib.request.urlretrieve(zip_url, output_zip)
        logging.info(f"Downloaded {output_zip}")
        with zipfile.ZipFile(output_zip, 'r') as zip_ref:
            zip_ref.extractall('.')
        logging.info("Extracted dictionaries.")
        os.remove(output_zip)
        logging.info("Removed zip file.")
    except Exception as e:
        logging.error(f"Failed to download/extract dictionaries: {e}")
        raise

# === Logging ===
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler()]
)

# === Constants ===
PROGNAME = "PAQJP_6.6"
HUFFMAN_THRESHOLD = 1024
PI_DIGITS_FILE = "pi_digits.txt"
PRIMES = [p for p in range(2, 256) if all(p % d != 0 for d in range(2, int(p**0.5)+1))]
MEM = 1 << 15
MIN_BITS = 2

# === Dictionary Files ===
DICTIONARY_FILES = [
    "words_enwik8.txt", "eng_news_2005_1M-sentences.txt", "eng_news_2005_1M-words.txt",
    "eng_news_2005_1M-sources.txt", "eng_news_2005_1M-co_n.txt",
    "eng_news_2005_1M-co_s.txt", "eng_news_2005_1M-inv_so.txt",
    "eng_news_2005_1M-meta.txt", "Dictionary.txt",
    "the-complete-reference-html-css-fifth-edition.txt", "francais.txt", "espanol.txt",
    "deutsch.txt", "ukenglish.txt", "vertebrate-palaeontology-dict.txt",
    "dictionary.2.bin", "dictionary.1.bin", "dictionary.3.bin", "dictionary.4.bin",
    "dictionary.6.bin", "dictionary.7.bin", "dictionary.8.bin", "dictionary.9.bin",
    "dictionary.11.bin", "dictionary.12.bin", "dictionary.13.bin", "dictionary.14.bin",
    "dictionary.15.bin", "dictionary.16.bin", "dictionary.19.bin", "dictionary.20.bin"
]

# === DNA Encoding Table ===
DNA_ENCODING_TABLE = {
    'AAAA': 0b00000, 'AAAC': 0b00001, 'AAAG': 0b00010, 'AAAT': 0b00011,
    'AACC': 0b00100, 'AACG': 0b00101, 'AACT': 0b00110, 'AAGG': 0b00111,
    'AAGT': 0b01000, 'AATT': 0b01001, 'ACCC': 0b01010, 'ACCG': 0b01011,
    'ACCT': 0b01100, 'AGGG': 0b01101, 'AGGT': 0b01110, 'AGTT': 0b01111,
    'CCCC': 0b10000, 'CCCG': 0b10001, 'CCCT': 0b10010, 'CGGG': 0b10011,
    'CGGT': 0b10100, 'CGTT': 0b10101, 'GTTT': 0b10110, 'CTTT': 0b10111,
    'AAAAAAAA': 0b11000, 'CCCCCCCC': 0b11001, 'GGGGGGGG': 0b11010, 'TTTTTTTT': 0b11011,
    'A': 0b11100, 'C': 0b11101, 'G': 0b11110, 'T': 0b11111
}
DNA_DECODING_TABLE = {v: k for k, v in DNA_ENCODING_TABLE.items()}

# === Pi Digits: ONLY 3 DIGITS (3.14) ===
def save_pi_digits(digits: List[int], filename: str = PI_DIGITS_FILE) -> bool:
    try:
        with open(filename, 'w') as f:
            f.write(','.join(str(d) for d in digits))
        logging.info(f"Saved {len(digits)} pi digits to {filename}")
        return True
    except Exception as e:
        logging.error(f"Failed to save pi digits: {e}")
        return False

def load_pi_digits(filename: str = PI_DIGITS_FILE, expected_count: int = 3) -> Optional[List[int]]:
    if not os.path.isfile(filename):
        return None
    try:
        with open(filename, 'r') as f:
            data = f.read().strip()
            digits = [int(x) for x in data.split(',') if x.isdigit()]
            if len(digits) != expected_count or any(d < 0 or d > 255 for d in digits):
                return None
            return digits
    except:
        return None

def generate_pi_digits(num_digits: int = 3, filename: str = PI_DIGITS_FILE) -> List[int]:
    try:
        from mpmath import mp
        mp.dps = num_digits + 5
        pi_str = str(mp.pi)[2:2 + num_digits]
        pi_digits = [int(d) for d in pi_str]
    except Exception:
        pi_digits = [3, 1, 4][:num_digits]
    mapped_digits = [(d * 255 // 9) % 256 for d in pi_digits]
    save_pi_digits(mapped_digits, filename)
    return mapped_digits

PI_DIGITS = generate_pi_digits(3)  # [85, 28, 113] → 3.14 mapped to 0–255

# === Helper Functions ===
class Filetype(Enum):
    DEFAULT = 0
    JPEG = 1
    TEXT = 3

class Node:
    def __init__(self, left=None, right=None, symbol=None):
        self.left = left
        self.right = right
        self.symbol = symbol
    def is_leaf(self):
        return self.left is None and self.right is None

def transform_with_prime_xor_every_3_bytes(data, repeat=100):
    t = bytearray(data)
    for prime in PRIMES:
        xor_val = prime if prime == 2 else max(1, math.ceil(prime * 4096 / 28672))
        for _ in range(repeat):
            for i in range(0, len(t), 3):
                t[i] ^= xor_val
    return bytes(t)

def transform_with_pattern_chunk(data, chunk_size=4):
    t = bytearray()
    for i in range(0, len(data), chunk_size):
        chunk = data[i:i + chunk_size]
        t.extend(b ^ 0xFF for b in chunk)
    return bytes(t)

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n ** 0.5) + 1, 2):
        if n % i == 0: return False
    return True

def find_nearest_prime_around(n):
    offset = 0
    while True:
        if is_prime(n - offset): return n - offset
        if is_prime(n + offset): return n + offset
        offset += 1

# === State Table (unchanged) ===
class StateTable:
    def __init__(self):
        self.table = [
            [1, 2, 0, 0], [3, 5, 1, 0], [4, 6, 0, 1], [7, 10, 2, 0],
            [8, 12, 1, 1], [9, 13, 1, 1], [11, 14, 0, 2], [15, 19, 3, 0],
            [16, 23, 2, 1], [17, 24, 2, 1], [18, 25, 2, 1], [20, 27, 1, 2],
            [21, 28, 1, 2], [22, 29, 1, 2], [26, 30, 0, 3], [31, 33, 4, 0],
            [32, 35, 3, 1], [32, 35, 3, 1], [32, 35, 3, 1], [32, 35, 3, 1],
            [34, 37, 2, 2], [34, 37, 2, 2], [34, 37, 2, 2], [34, 37, 2, 2],
            [34, 37, 2, 2], [34, 37, 2, 2], [36, 39, 1, 3], [36, 39, 1, 3],
            [36, 39, 1, 3], [36, 39, 1, 3], [38, 40, 0, 4], [41, 43, 5, 0],
            [42, 45, 4, 1], [42, 45, 4, 1], [44, 47, 3, 2], [44, 47, 3, 2],
            [46, 49, 2, 3], [46, 49, 2, 3], [48, 51, 1, 4], [48, 51, 1, 4],
            [50, 52, 0, 5], [53, 43, 6, 0], [54, 57, 5, 1], [54, 57, 5, 1],
            [56, 59, 4, 2], [56, 59, 4, 2], [58, 61, 3, 3], [58, 61, 3, 3],
            [60, 63, 2, 4], [60, 63, 2, 4], [62, 65, 1, 5], [62, 65, 1, 5],
            [50, 66, 0, 6], [67, 55, 7, 0], [68, 57, 6, 1], [68, 57, 6, 1],
            [70, 73, 5, 2], [70, 73, 5, 2], [72, 75, 4, 3], [72, 75, 4, 3],
            [74, 77, 3, 4], [74, 77, 3, 4], [76, 79, 2, 5], [76, 79, 2, 5],
            [62, 81, 1, 6], [62, 81, 1, 6], [64, 82, 0, 7], [83, 69, 8, 0],
            [84, 76, 7, 1], [84, 76, 7, 1], [86, 73, 6, 2], [86, 73, 6, 2],
            [44, 59, 5, 3], [44, 59, 5, 3], [58, 61, 4, 4], [58, 61, 4, 4],
            [60, 49, 3, 5], [60, 49, 3, 5], [76, 89, 2, 6], [76, 89, 2, 6],
            [78, 91, 1, 7], [78, 91, 1, 7], [80, 92, 0, 8], [93, 69, 9, 0],
            [94, 87, 8, 1], [94, 87, 8, 1], [96, 45, 7, 2], [96, 45, 7, 2],
            [48, 99, 2, 7], [48, 99, 2, 7], [88, 101, 1, 8], [88, 101, 1, 8],
            [80, 102, 0, 9], [103, 69, 10, 0], [104, 87, 9, 1], [104, 87, 9, 1],
            [106, 57, 8, 2], [106, 57, 8, 2], [62, 109, 2, 8], [62, 109, 2, 8],
            [88, 111, 1, 9], [88, 111, 1, 9], [80, 112, 0, 10], [113, 85, 11, 0],
            [114, 87, 10, 1], [114, 87, 10, 1], [116, 57, 9, 2], [116, 57, 9, 2],
            [62, 119, 2, 9], [62, 119, 2, 9], [88, 121, 1, 10], [88, 121, 1, 10],
            [90, 122, 0, 11], [123, 85, 12, 0], [124, 97, 11, 1], [124, 97, 11, 1],
            [126, 57, 10, 2], [126, 57, 10, 2], [62, 129, 2, 10], [62, 129, 2, 10],
            [98, 131, 1, 11], [98, 131, 1, 11], [90, 132, 0, 12], [133, 85, 13, 0],
            [134, 97, 12, 1], [134, 97, 12, 1], [136, 57, 11, 2], [136, 57, 11, 2],
            [62, 139, 2, 11], [62, 139, 2, 11], [98, 141, 1, 12], [98, 141, 1, 12],
            [90, 142, 0, 13], [143, 95, 14, 0], [144, 97, 13, 1], [144, 97, 13, 1],
            [68, 57, 12, 2], [68, 57, 12, 2], [62, 81, 2, 12], [62, 81, 2, 12],
            [98, 147, 1, 13], [98, 147, 1, 13], [100, 148, 0, 14], [149, 95, 15, 0],
            [150, 107, 14, 1], [150, 107, 14, 1], [108, 151, 1, 14], [108, 151, 1, 14],
            [100, 152, 0, 15], [153, 95, 16, 0], [154, 107, 15, 1], [108, 155, 1, 15],
            [100, 156, 0, 16], [157, 95, 17, 0], [158, 107, 16, 1], [108, 159, 1, 16],
            [100, 160, 0, 17], [161, 105, 18, 0], [162, 107, 17, 1], [108, 163, 1, 17],
            [110, 164, 0, 18], [165, 105, 19, 0], [166, 117, 18, 1], [118, 167, 1, 18],
            [110, 168, 0, 19], [169, 105, 20, 0], [170, 117, 19, 1], [118, 171, 1, 19],
            [110, 172, 0, 20], [173, 105, 21, 0], [174, 117, 20, 1], [118, 175, 1, 20],
            [110, 176, 0, 21], [177, 105, 22, 0], [178, 117, 21, 1], [118, 179, 1, 21],
            [120, 184, 0, 23], [185, 115, 24, 0], [186, 127, 23, 1], [128, 187, 1, 23],
            [120, 188, 0, 24], [189, 115, 25, 0], [190, 127, 24, 1], [128, 191, 1, 24],
            [120, 192, 0, 25], [193, 115, 26, 0], [194, 127, 25, 1], [128, 195, 1, 25],
            [120, 196, 0, 26], [197, 115, 27, 0], [198, 127, 26, 1], [128, 199, 1, 26],
            [120, 200, 0, 27], [201, 115, 28, 0], [202, 127, 27, 1], [128, 203, 1, 27],
            [120, 204, 0, 28], [205, 115, 29, 0], [206, 127, 28, 1], [128, 207, 1, 28],
            [120, 208, 0, 29], [209, 125, 30, 0], [210, 127, 29, 1], [128, 211, 1, 29],
            [130, 212, 0, 30], [213, 125, 31, 0], [214, 137, 30, 1], [138, 215, 1, 30],
            [130, 216, 0, 31], [217, 125, 32, 0], [218, 137, 31, 1], [138, 219, 1, 31],
            [130, 220, 0, 32], [221, 125, 33, 0], [222, 137, 32, 1], [138, 223, 1, 32],
            [130, 224, 0, 33], [225, 125, 34, 0], [226, 137, 33, 1], [138, 227, 1, 33],
            [130, 228, 0, 34], [229, 125, 35, 0], [230, 137, 34, 1], [138, 231, 1, 34],
            [130, 232, 0, 35], [233, 125, 36, 0], [234, 137, 35, 1], [138, 235, 1, 35],
            [130, 236, 0, 36], [237, 125, 37, 0], [238, 137, 36, 1], [138, 239, 1, 36],
            [130, 240, 0, 37], [241, 125, 38, 0], [242, 137, 37, 1], [138, 243, 1, 37],
            [130, 244, 0, 38], [245, 135, 39, 0], [246, 137, 38, 1], [138, 247, 1, 38],
            [140, 248, 0, 39], [249, 135, 40, 0], [250, 69, 39, 1], [80, 251, 1, 39],
            [140, 252, 0, 40], [249, 135, 41, 0], [250, 69, 40, 1], [80, 251, 1, 40],
            [140, 252, 0, 41]
        ]

# === Smart Compressor (Optional) ===
class SmartCompressor:
    def __init__(self):
        if not any(os.path.exists(f) for f in DICTIONARY_FILES):
            download_dictionaries()
        self.dictionaries = self.load_dictionaries()

    def load_dictionaries(self):
        data = []
        for f in DICTIONARY_FILES:
            if os.path.exists(f):
                try:
                    if f.endswith('.bin'):
                        with open(f, 'rb') as fp:
                            data.append(binascii.hexlify(fp.read()).decode('ascii'))
                    else:
                        with open(f, 'r', encoding='utf-8', errors='ignore') as fp:
                            data.append(fp.read())
                except: pass
        return data

    def compute_sha256_binary(self, data):
        return hashlib.sha256(data).digest()

    def paq_compress(self, data):
        try: return paq.compress(data)
        except: return None

    def paq_decompress(self, data):
        try: return paq.decompress(data)
        except: return None

    def reversible_transform(self, data):
        return bytes(b ^ 0xAA for b in data)

    def compress(self, input_data, input_file):
        if not input_data: return bytes([0])
        if isinstance(input_data, str): input_data = input_data.encode('utf-8')
        transformed = self.reversible_transform(input_data)
        compressed = self.paq_compress(transformed)
        if compressed and len(compressed) < len(input_data):
            return self.compute_sha256_binary(input_data) + compressed
        return None

    def decompress(self, input_data):
        if len(input_data) < 32: return None
        stored_hash, compressed = input_data[:32], input_data[32:]
        decompressed = self.paq_decompress(compressed)
        if not decompressed: return None
        original = self.reversible_transform(decompressed)
        if hashlib.sha256(original).digest() == stored_hash:
            return original
        return None

# === PAQJP Compressor (Main) ===
class PAQJPCompressor:
    def __init__(self):
        self.PI_DIGITS = PI_DIGITS.copy()
        self.PRIMES = PRIMES
        self.seed_tables = self.generate_seed_tables()
        self.SQUARE_OF_ROOT = 2
        self.ADD_NUMBERS = 1
        self.MULTIPLY = 3
        self.fibonacci = self.generate_fibonacci(100)
        self.state_table = StateTable()

    def generate_fibonacci(self, n: int) -> List[int]:
        fib = [0, 1]
        for i in range(2, n):
            fib.append((fib[i-1] + fib[i-2]) % 256)
        return fib

    def generate_seed_tables(self, num_tables=126, table_size=256, min_val=5, max_val=255, seed=42):
        random.seed(seed)
        return [[random.randint(min_val, max_val) for _ in range(table_size)] for _ in range(num_tables)]

    def get_seed(self, table_idx: int, value: int) -> int:
        if 0 <= table_idx < len(self.seed_tables):
            return self.seed_tables[table_idx][value % 256]
        return 0

    def create_quantum_transform_circuit(self, transform_idx: int, data_length: int):
        if qiskit is None: return
        try:
            circuit = qiskit.QuantumCircuit(9)
            for i in range(9): circuit.h(i)
            theta = (transform_idx * data_length) % 512 / 512 * math.pi
            for i in range(9): circuit.ry(theta, i)
            for i in range(8): circuit.cx(i, i + 1)
        except: pass

    def calculate_frequencies(self, s): 
        return {c: s.count(c) for c in set(s)} if s else {}

    def build_huffman_tree(self, freq):
        if not freq: return None
        heap = [(f, Node(symbol=s)) for s, f in freq.items()]
        heapq.heapify(heap)
        while len(heap) > 1:
            f1, n1 = heapq.heappop(heap)
            f2, n2 = heapq.heappop(heap)
            heapq.heappush(heap, (f1 + f2, Node(n1, n2)))
        return heap[0][1]

    def generate_huffman_codes(self, root, code="", codes={}):
        if root.is_leaf():
            codes[root.symbol] = code or "0"
            return codes
        self.generate_huffman_codes(root.left, code + "0", codes)
        self.generate_huffman_codes(root.right, code + "1", codes)
        return codes

    def compress_data_huffman(self, s):
        if not s: return ""
        freq = self.calculate_frequencies(s)
        tree = self.build_huffman_tree(freq)
        codes = self.generate_huffman_codes(tree)
        return ''.join(codes.get(c, "0") for c in s)

    def decompress_data_huffman(self, s):
        if not s: return ""
        freq = self.calculate_frequencies(s)
        tree = self.build_huffman_tree(freq)
        codes = self.generate_huffman_codes(tree)
        rev = {v: k for k, v in codes.items()}
        out, cur = "", ""
        for c in s:
            cur += c
            if cur in rev:
                out += rev[cur]
                cur = ""
        return out

    def transform_genomecompress(self, data: bytes) -> bytes:
        try: dna = data.decode('ascii').upper()
        except: return b''
        if not all(c in 'ACGT' for c in dna): return b''
        bits, i = [], 0
        while i < len(dna):
            seg = dna[i:i+8]
            if seg in DNA_ENCODING_TABLE:
                bits.extend(format(DNA_ENCODING_TABLE[seg], '05b'))
                i += 8
            else:
                seg = dna[i]
                bits.extend(format(DNA_ENCODING_TABLE[seg], '05b'))
                i += 1
        bitstr = ''.join(bits)
        return int(bitstr, 2).to_bytes((len(bitstr)+7)//8, 'big') if bitstr else b''

    def reverse_transform_genomecompress(self, data: bytes) -> bytes:
        if not data: return b''
        bitstr = bin(int.from_bytes(data, 'big'))[2:].zfill(len(data)*8)
        out, i = [], 0
        while i + 5 <= len(bitstr):
            code = int(bitstr[i:i+5], 2)
            if code in DNA_DECODING_TABLE:
                out.append(DNA_DECODING_TABLE[code])
                i += 5
            else: break
        return ''.join(out).encode('ascii')

    def transform_01(self, data, repeat=100): return transform_with_prime_xor_every_3_bytes(data, repeat)
    def reverse_transform_01(self, data, repeat=100): return self.transform_01(data, repeat)

    def transform_03(self, data): return transform_with_pattern_chunk(data)
    def reverse_transform_03(self, data): return self.transform_03(data)

    def transform_04(self, data, repeat=100):
        t = bytearray(data)
        for _ in range(repeat):
            for i in range(len(t)): t[i] = (t[i] - (i % 256)) % 256
        return bytes(t)
    def reverse_transform_04(self, data, repeat=100):
        t = bytearray(data)
        for _ in range(repeat):
            for i in range(len(t)): t[i] = (t[i] + (i % 256)) % 256
        return bytes(t)

    def transform_05(self, data, shift=3):
        t = bytearray(data)
        for i in range(len(t)):
            t[i] = ((t[i] << shift) | (t[i] >> (8 - shift))) & 0xFF
        return bytes(t)
    def reverse_transform_05(self, data, shift=3):
        t = bytearray(data)
        for i in range(len(t)):
            t[i] = ((t[i] >> shift) | (t[i] << (8 - shift))) & 0xFF
        return bytes(t)

    def transform_06(self, data, seed=42):
        random.seed(seed)
        sub = list(range(256))
        random.shuffle(sub)
        return bytes(sub[b] for b in data)
    def reverse_transform_06(self, data, seed=42):
        random.seed(seed)
        sub = list(range(256))
        random.shuffle(sub)
        rev = [0]*256
        for i, v in enumerate(sub): rev[v] = i
        return bytes(rev[b] for b in data)

    def transform_07(self, data, repeat=100):
        t = bytearray(data)
        pi_len = len(self.PI_DIGITS)
        shift = len(data) % pi_len
        pi_rot = self.PI_DIGITS[shift:] + self.PI_DIGITS[:shift]
        size_byte = len(data) % 256
        cycles = min(10, max(1, len(data)//1024))
        for i in range(len(t)): t[i] ^= size_byte
        for _ in range(cycles * repeat // 10):
            for i in range(len(t)): t[i] ^= pi_rot[i % pi_len]
        return bytes(t)
    def reverse_transform_07(self, data, repeat=100):
        t = bytearray(data)
        pi_len = len(self.PI_DIGITS)
        shift = len(data) % pi_len
        pi_rot = self.PI_DIGITS[shift:] + self.PI_DIGITS[:shift]
        size_byte = len(data) % 256
        cycles = min(10, max(1, len(data)//1024))
        for _ in range(cycles * repeat // 10):
            for i in range(len(t)): t[i] ^= pi_rot[i % pi_len]
        for i in range(len(t)): t[i] ^= size_byte
        return bytes(t)

    def transform_08(self, data, repeat=100): return self.transform_07(data, repeat)  # Same logic
    def reverse_transform_08(self, data, repeat=100): return self.reverse_transform_07(data, repeat)

    def transform_09(self, data, repeat=100): return self.transform_07(data, repeat)
    def reverse_transform_09(self, data, repeat=100): return self.reverse_transform_07(data, repeat)

    def transform_10(self, data, repeat=100):
        count = sum(1 for i in range(len(data)-1) if data[i:i+2] == b'X1')
        n = (((count * 2) + 1) // 3) * 3 % 256
        t = bytearray(b ^ n for b in data)
        return bytes([n]) + bytes(t)
    def reverse_transform_10(self, data, repeat=100):
        if len(data) < 1: return b''
        n = data[0]
        return bytes(b ^ n for b in data[1:])

    def transform_12(self, data, repeat=100):
        t = bytearray(data)
        fib_len = len(self.fibonacci)
        for _ in range(repeat):
            for i in range(len(t)): t[i] ^= self.fibonacci[i % fib_len]
        return bytes(t)
    def reverse_transform_12(self, data, repeat=100): return self.transform_12(data, repeat)

    def generate_transform_method(self, n):
        self.create_quantum_transform_circuit(n, 1048576)
        seed_idx = n % len(self.seed_tables)
        def transform(data, repeat=100):
            seed = self.get_seed(seed_idx, len(data))
            return bytes(b ^ seed for b in data)
        return transform, transform

    def compress_with_best_method(self, data, filetype, filename, mode="slow"):
        if not data: return bytes([0])
        if isinstance(data, str): data = data.encode('utf-8')

        is_dna = data.decode('ascii', errors='ignore').upper().strip('ACGT\n') == ''

        fast = [(1,self.transform_04),(2,self.transform_01),(3,self.transform_03),(5,self.transform_05),(6,self.transform_06),(7,self.transform_07),(8,self.transform_08),(9,self.transform_09),(12,self.transform_12)]
        slow = fast + [(10,self.transform_10)] + [(i,self.generate_transform_method(i)[0]) for i in range(16,256)]
        transformations = [(0,self.transform_genomecompress)] + slow if is_dna else (slow if mode == "slow" else fast)

        best, best_size, best_marker = None, float('inf'), None
        for marker, tfunc in transformations:
            try:
                compressed = paq.compress(tfunc(data))
                if compressed and len(compressed) < best_size:
                    best, best_size, best_marker = compressed, len(compressed), marker
            except: continue

        if len(data) < HUFFMAN_THRESHOLD:
            bits = bin(int.from_bytes(data, 'big'))[2:].zfill(len(data)*8)
            h = self.compress_data_huffman(bits)
            hb = int(h, 2).to_bytes((len(h)+7)//8, 'big') if h else b''
            if hb and len(hb) < best_size:
                best, best_size, best_marker = hb, len(hb), 4

        return bytes([best_marker]) + (best or data) if best else bytes([0]) + data

    def decompress_with_best_method(self, data):
        if len(data) < 1: return b'', None
        marker, payload = data[0], data[1:]
        rev = {
            0: self.reverse_transform_genomecompress,
            1: self.reverse_transform_04, 2: self.reverse_transform_01, 3: self.reverse_transform_03,
            5: self.reverse_transform_05, 6: self.reverse_transform_06, 7: self.reverse_transform_07,
            8: self.reverse_transform_08, 9: self.reverse_transform_09, 10: self.reverse_transform_10,
            12: self.reverse_transform_12,
        }
        rev.update({i: self.generate_transform_method(i)[1] for i in range(16,256)})

        if marker == 4:
            bits = bin(int.from_bytes(payload, 'big'))[2:].zfill(len(payload)*8)
            out = self.decompress_data_huffman(bits)
            return int(out, 2).to_bytes((len(out)+7)//8, 'big'), 4

        if marker not in rev: return b'', None
        try:
            decompressed = paq.decompress(payload)
            return rev[marker](decompressed), marker
        except: return b'', None

    def compress(self, in_file, out_file, filetype=Filetype.DEFAULT, mode="slow"):
        try:
            with open(in_file, 'rb') as f: data = f.read()
            if not data: return False
            compressed = self.compress_with_best_method(data, filetype, in_file, mode)
            with open(out_file, 'wb') as f: f.write(compressed)
            return True
        except Exception as e:
            logging.error(f"Compress error: {e}")
            return False

    def decompress(self, in_file, out_file):
        try:
            with open(in_file, 'rb') as f: data = f.read()
            if not data: return False
            decompressed, _ = self.decompress_with_best_method(data)
            if not decompressed: return False
            with open(out_file, 'wb') as f: f.write(decompressed)
            return True
        except Exception as e:
            logging.error(f"Decompress error: {e}")
            return False

# === Filetype Detection ===
def detect_filetype(name):
    ext = os.path.splitext(name.lower())[1]
    if ext in ['.jpg', '.jpeg']: return Filetype.JPEG
    if ext in ['.txt', '.dna']: return Filetype.TEXT
    return Filetype.DEFAULT

# === Main ===
def main():
    print("PAQJP_6.6 - 252 Lossless Transforms")
    print("1: Compress | 2: Decompress")
    comp = PAQJPCompressor()
    choice = input("Choice: ").strip()
    if choice == '1':
        mode = "slow" if input("Mode (1=fast, 2=slow): ").strip() != '1' else "fast"
        in_f = input("Input file: ").strip()
        out_f = input("Output file: ").strip()
        if comp.compress(in_f, out_f, detect_filetype(in_f), mode):
            print(f"Compressed: {out_f}")
        else: print("Failed")
    elif choice == '2':
        in_f = input("Input file: ").strip()
        out_f = input("Output file: ").strip()
        if comp.decompress(in_f, out_f):
            print(f"Decompressed: {out_f}")
        else: print("Failed")

if __name__ == "__main__":
    main()
