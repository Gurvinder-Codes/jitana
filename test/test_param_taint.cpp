/*
 * Copyright (c) 2024
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
 * OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 */

#define BOOST_TEST_MODULE test_param_taint
#define BOOST_TEST_INCLUDED
#include <boost/test/unit_test.hpp>

#include <array>

#include <jitana/jitana.hpp>
#include <jitana/analysis/interproc_param_taint.hpp>
#include <jitana/vm_core/access_flags.hpp>
#include <jitana/vm_core/opcode.hpp>
#include <jitana/vm_graph/insn_graph.hpp>

using namespace jitana;

namespace {
    insn_vertex_descriptor add_vertex_with(uint32_t off,
                                           const insn& i,
                                           insn_graph& g)
    {
        auto v = add_vertex(g);
        g[v].off = off;
        g[v].insn = i;
        return v;
    }

    insn_graph make_identity_body(const dex_method_hdl& dex_hdl,
                                  const jvm_method_hdl& jvm_hdl)
    {
        insn_graph g;
        g[boost::graph_bundle].hdl = dex_hdl;
        g[boost::graph_bundle].jvm_hdl = jvm_hdl;
        g[boost::graph_bundle].registers_size = 1;
        g[boost::graph_bundle].ins_size = 1;
        g[boost::graph_bundle].outs_size = 0;

        std::array<register_idx, 5> entry_regs;
        entry_regs.fill(register_idx::idx_unknown);
        entry_regs.front() = 0;
        entry_regs.back() = 0;

        auto entry = add_vertex_with(0, insn_entry(opcode::op_nop, entry_regs, {}),
                                     g);
        auto ret = add_vertex_with(1, insn_return(opcode::op_return, {{0}}, {}),
                                   g);
        auto exit_v = add_vertex_with(
                2, insn_exit(opcode::op_nop, {{register_idx::idx_result}}, {}),
                g);

        add_edge(entry, ret, insn_control_flow_edge_property(), g);
        add_edge(ret, exit_v, insn_control_flow_edge_property(), g);
        return g;
    }

    method_vertex_descriptor add_method(virtual_machine& vm,
                                        const dex_method_hdl& dex_hdl,
                                        const jvm_method_hdl& jvm_hdl,
                                        insn_graph ig)
    {
        method_vertex_property prop;
        prop.hdl = dex_hdl;
        prop.jvm_hdl = jvm_hdl;
        prop.class_hdl = {dex_hdl.file_hdl, 0};
        prop.access_flags = acc_public;
        prop.insns = std::move(ig);

        auto mv = add_vertex(prop, vm.methods());
        vm.methods()[boost::graph_bundle].hdl_to_vertex[dex_hdl] = mv;
        vm.methods()[boost::graph_bundle].jvm_hdl_to_vertex[jvm_hdl] = mv;
        return mv;
    }
}

BOOST_AUTO_TEST_CASE(param_taint_interprocedural)
{
    virtual_machine vm;

    class_loader_hdl loader{2};
    dex_file_hdl file_hdl{loader, 0};
    jvm_type_hdl type_hdl{loader, "LTest2;"};

    dex_method_hdl callee_hdl{file_hdl, 0};
    dex_method_hdl caller_hdl{file_hdl, 1};

    jvm_method_hdl callee_jvm{type_hdl, "id(I)I"};
    jvm_method_hdl caller_jvm{type_hdl, "caller(I)I"};

    auto callee_mv
            = add_method(vm, callee_hdl, callee_jvm,
                         make_identity_body(callee_hdl, callee_jvm));
    (void)callee_mv;

    // caller: param in v1, invoke id, move-result v0, return v0
    insn_graph g;
    g[boost::graph_bundle].hdl = caller_hdl;
    g[boost::graph_bundle].jvm_hdl = caller_jvm;
    g[boost::graph_bundle].registers_size = 2;
    g[boost::graph_bundle].ins_size = 1;
    g[boost::graph_bundle].outs_size = 0;

    std::array<register_idx, 5> entry_regs;
    entry_regs.fill(register_idx::idx_unknown);
    entry_regs.front() = 1;
    entry_regs.back() = 1;
    auto e = add_vertex_with(0, insn_entry(opcode::op_nop, entry_regs, {}), g);

    std::array<register_idx, 5> call_regs;
    call_regs.fill(register_idx::idx_unknown);
    call_regs[0] = 1;
    auto call = add_vertex_with(
            1, insn_invoke(opcode::op_invoke_static, call_regs, callee_hdl), g);
    auto mv_res = add_vertex_with(
            2, insn_move(opcode::op_move_result,
                         {{register_idx(0), register_idx::idx_result}}, {}),
            g);
    auto ret = add_vertex_with(3, insn_return(opcode::op_return, {{0}}, {}), g);
    auto x = add_vertex_with(
            4, insn_exit(opcode::op_nop, {{register_idx::idx_result}}, {}), g);

    add_edge(e, call, insn_control_flow_edge_property(), g);
    add_edge(call, mv_res, insn_control_flow_edge_property(), g);
    add_edge(mv_res, ret, insn_control_flow_edge_property(), g);
    add_edge(ret, x, insn_control_flow_edge_property(), g);

    add_method(vm, caller_hdl, caller_jvm, std::move(g));

    analysis::dfa::InterprocParamConfig cfg;
    auto result = analysis::dfa::run_interproc_param_taint(vm, cfg);

    auto mid = analysis::dfa::make_method_id(caller_jvm);
    auto it = result.summaries.find(mid);
    BOOST_REQUIRE(it != result.summaries.end());
    BOOST_CHECK(it->second.return_dep.test(0));
}
