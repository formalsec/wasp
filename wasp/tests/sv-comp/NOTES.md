# PROBLEMS

* `array-fpi`: 
  * `indp1`: overflow
* `array-patterns`:
  * Some crashes?

# TODO
* Use cvtops to avoid casting type during z3encoding
* `reverse_array_alloca`: wow
* `cstrcat_unsafe`: not supported
* `array-realloc-3`: valid-memtrack

# Benchmark Table

## ReachSafety - Arrays

|          DirName          | Results t10 |
|:-------------------------:|:-----------:|
|       `array-cav19`       |    11/13    |
|      `array-crafted`      |    35/43    |
|     `array-examples`      |    67/95    |
|        `array-fpi`        |   135/138   |
| `array-industry-pattern`  |    11/17    |
| `array-lopstr16`          |    11/11    |
| `array-multidimensional`  |    20/20    |
| `array-pattern`           |    20/30    |
| `array-programs`          |    13/16    |
| `array-tiling`            |    26/29    |

## ReachSafety - BitVectors

|          DirName          | Results t10 |
|:-------------------------:|:-----------:|
| `bitvector`               |    34/51    |
| `bitvector-loops`         |     2/3     |
| `bitvector-regression`    |    10/10    |

## ReachSafety - Floats

|          DirName          | Results t10 |
|:-------------------------:|:-----------:|
| `float-benchs`            |    43/82    |
| `float-newlib`            |   258/265   |
| `floats-cbmc-regression`  |    14/16    |
|      `floats-cdfpl`       |             |
| `floats-esbmc-regression` |             |
|      `forester-heap`      |             |
|        `heap-data`        |             |
|   `list-ext-properties`   |             |

## MemorySafety
|          DirName          | Results t10 |
|:-------------------------:|:-----------:|
| `array-memsafety`         |    ****     |
| `array-memsafety-realloc` |    ****     |

