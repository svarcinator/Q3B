#pragma once
#include <iostream>
#include <sstream>

#include "Caches.h"

class CacheFormatter {
public:
    

    static std::stringstream 
    cacheHitsToJson(const Caches::CacheHits& cacheHits) {
        std::stringstream ss;
        ss << "{";

        ss << "bvecExpr :" <<  cacheHits.bvecExprCacheHits << std::endl;
        ss << "sameBWPreciseBvecs:" << cacheHits.sameBWPreciseBvecsHits << std::endl;
        ss << "prevBWpreciseBvecs :" << cacheHits.prevBWpreciseBvecsHits << std::endl;
        ss << "intervals :" << cacheHits.intervalsHits << std::endl;
        ss << "bddExpr :" << cacheHits.bddExprCacheHits << std::endl;
        ss << "sameBWPreciseBdds :" << cacheHits.sameBWPreciseBddsHits << std::endl;
        ss << "sameBWImpreciseBvecStates :" << cacheHits.sameBWImpreciseBvecStatesHits << std::endl;

        ss << "}";
        return ss;
    }

    static std::stringstream
     cacheSizesToJson(const Caches& caches) {
        std::stringstream ss;
        ss << "{";

        ss << "bvecExpr :" <<  caches.bvecExprCache.size() << std::endl;
        ss << "sameBWPreciseBvecs :" << caches.sameBWPreciseBvecs.size() << std::endl;
        ss << "prevBWpreciseBvecs :" << caches.prevBWpreciseBvecs.size() << std::endl;
        ss << "intervals :" << caches.intervals.size() << std::endl;
        ss << "bddExpr :" << caches.bddExprCache.size() << std::endl;
        ss << "sameBWPreciseBdds :" << caches.sameBWPreciseBdds.size() << std::endl;
        ss << "sameBWImpreciseBvecStates :" << caches.sameBWImpreciseBvecStates.size() << std::endl;

        ss << "}";
        return ss;
    }
};
