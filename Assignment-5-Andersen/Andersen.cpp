/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A5Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump("ConstraintGraph");

    Andersen andersen(consg);

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // 初始化工作列表
    WorkList<SVF::ConstraintEdge*> worklist;
    
    // 1. 初始化阶段：处理地址约束和收集所有约束边
    for (auto it = consg->begin(); it != consg->end(); ++it) {
        SVF::ConstraintNode* node = it->second;
        
        // 处理地址约束（Addr edges）- 根据第2张图的getAddrInEdges()
        for (auto* edge : node->getAddrInEdges()) {
            // 使用第3张图的类型转换方法
            if (SVF::AddrCGEdge* addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge)) {
                unsigned src = addrEdge->getSrcID();
                unsigned dst = addrEdge->getDstID();
                pts[dst].insert(src);
            }
        }
        
        // 将所有约束边加入工作列表（根据第2张图的各种边类型）
        // 复制边
        for (auto* edge : node->getCopyInEdges()) {
            worklist.push(edge);
        }
        for (auto* edge : node->getCopyOutEdges()) {
            worklist.push(edge);
        }
        // 加载边
        for (auto* edge : node->getLoadInEdges()) {
            worklist.push(edge);
        }
        for (auto* edge : node->getLoadOutEdges()) {
            worklist.push(edge);
        }
        // 存储边
        for (auto* edge : node->getStoreInEdges()) {
            worklist.push(edge);
        }
        for (auto* edge : node->getStoreOutEdges()) {
            worklist.push(edge);
        }
    }

    // 2. 迭代求解阶段
    while (!worklist.empty()) {
        SVF::ConstraintEdge* edge = worklist.pop();
        
        // 使用第3张图的类型转换方法处理不同类型的边
        if (SVF::CopyCGEdge* copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge)) {
            // 处理复制约束：a = b
            unsigned src = copyEdge->getSrcID();
            unsigned dst = copyEdge->getDstID();
            
            auto& srcPts = pts[src];
            auto& dstPts = pts[dst];
            bool changed = false;
            
            // 将src的指向集合并到dst
            for (unsigned obj : srcPts) {
                if (dstPts.insert(obj).second) {
                    changed = true;
                }
            }
            
            // 如果发生变化，传播到相关边
            if (changed) {
                SVF::ConstraintNode* dstNode = consg->getConstraintNode(dst);
                for (auto* e : dstNode->getCopyOutEdges()) worklist.push(e);
                for (auto* e : dstNode->getLoadOutEdges()) worklist.push(e);
                for (auto* e : dstNode->getStoreInEdges()) worklist.push(e);
            }
        }
        else if (SVF::LoadCGEdge* loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge)) {
            // 处理加载约束：a = *b
            unsigned src = loadEdge->getSrcID();
            unsigned dst = loadEdge->getDstID();
            
            auto& srcPts = pts[src];
            auto& dstPts = pts[dst];
            bool changed = false;
            
            for (unsigned obj : srcPts) {
                auto& objPts = pts[obj];
                for (unsigned pointedObj : objPts) {
                    if (dstPts.insert(pointedObj).second) {
                        changed = true;
                    }
                }
            }
            
            if (changed) {
                SVF::ConstraintNode* dstNode = consg->getConstraintNode(dst);
                for (auto* e : dstNode->getCopyOutEdges()) worklist.push(e);
                for (auto* e : dstNode->getLoadOutEdges()) worklist.push(e);
                for (auto* e : dstNode->getStoreInEdges()) worklist.push(e);
            }
        }
        else if (SVF::StoreCGEdge* storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge)) {
            // 处理存储约束：*a = b
            unsigned src = storeEdge->getSrcID();
            unsigned dst = storeEdge->getDstID();
            
            auto& srcPts = pts[src];
            auto& dstPts = pts[dst];
            bool changed = false;
            
            for (unsigned obj : dstPts) {
                auto& objPts = pts[obj];
                for (unsigned srcObj : srcPts) {
                    if (objPts.insert(srcObj).second) {
                        changed = true;
                    }
                }
                
                if (changed) {
                    SVF::ConstraintNode* objNode = consg->getConstraintNode(obj);
                    for (auto* e : objNode->getCopyOutEdges()) worklist.push(e);
                    for (auto* e : objNode->getLoadOutEdges()) worklist.push(e);
                    for (auto* e : objNode->getStoreInEdges()) worklist.push(e);
                }
            }
        }
    }
}