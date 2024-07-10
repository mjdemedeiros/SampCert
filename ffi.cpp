#include <lean/lean.h>

extern "C" uint32_t extern_probPure(uint32_t a,) {
    return a;
}

// extern "C" uint32_t extern_probBind(uint32_t a, uint32_t b) {
//     return 0;
// }
//
// extern "C" uint32_t extern_UniformPowerOfTwoSample(uint32_t a, uint32_t b) {
//     return 0;
// }
//
// extern "C" uint32_t extern_probWhile(uint32_t a, uint32_t b) {
//     return 0;
// }
