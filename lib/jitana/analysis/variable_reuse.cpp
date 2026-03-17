#include <jitana/analysis/variable_reuse.hpp>

#include <algorithm>
#include <limits>

namespace jitana {
namespace analysis {
namespace dfa {

namespace {

    // Build coarse live ranges [first,last] for each register based on LIVE_IN / LIVE_OUT.
    std::vector<std::pair<int,int>>
    build_live_ranges(const LivenessResult& L)
    {
        const std::size_t N = L.order.size();
        const std::size_t R = L.reg_domain;

        // Initialize with "no use": ( +inf, -inf ) so we can tighten.
        const int INF = std::numeric_limits<int>::max();
        std::vector<std::pair<int,int>> ranges(R, {INF, -INF});

        for (std::size_t i = 0; i < N; ++i) {
            const auto& in  = L.LIVE_IN[i];
            const auto& out = L.LIVE_OUT[i];

            for (std::size_t r = 0; r < R; ++r) {
                if (in.test(r) || out.test(r)) {
                    auto& range = ranges[r];
                    auto& first = range.first;
                    auto& last = range.second;
                    if (static_cast<int>(i) < first) first = static_cast<int>(i);
                    if (static_cast<int>(i) > last)  last  = static_cast<int>(i);
                }
            }
        }

        // Convert unused registers from (INF, -INF) to (-1, -1) for clarity.
        for (auto& range : ranges) {
            auto& first = range.first;
            auto& last = range.second;
            if (first == INF && last == -INF) {
                first = -1;
                last  = -1;
            }
        }

        return ranges;
    }

    constexpr bool unused(const std::pair<int, int>& range)
    {
        return range.first < 0 || range.second < 0;
    }

    // Check if two live ranges [a1,a2] and [b1,b2] overlap.
    bool disjoint_ranges(const std::pair<int,int>& a,
                         const std::pair<int,int>& b)
    {
        if (unused(a) || unused(b)) {
            return false;
        }
        const int a1 = a.first;
        const int a2 = a.second;
        const int b1 = b.first;
        const int b2 = b.second;
        // Overlap if: max(start) <= min(end)
        const int start = std::max(a1, b1);
        const int end   = std::min(a2, b2);
        return !(start <= end);
    }

}

ReuseResult run_variable_reuse(::jitana::virtual_machine& vm,
                               const ::jitana::method_vertex_descriptor& mv,
                               const LivenessResult& L)
{
    ReuseResult result;
    result.reg_domain = L.reg_domain;

    result.live_ranges = build_live_ranges(L);

    const std::size_t R = result.reg_domain;

    for (std::size_t r1 = 0; r1 < R; ++r1) {
        for (std::size_t r2 = r1 + 1; r2 < R; ++r2) {
            const auto& a = result.live_ranges[r1];
            const auto& b = result.live_ranges[r2];

            if (unused(a) || unused(b)) {
                continue;
            }

            if (disjoint_ranges(a, b)) {
                ReusePair pair;
                pair.reg_a = static_cast<int>(r1);
                pair.reg_b = static_cast<int>(r2);
                pair.note  = "Non-overlapping live ranges (can potentially share one register).";
                result.disjoint_pairs.push_back(pair);
            }
        }
    }

    return result;
}

} 
} 
}
