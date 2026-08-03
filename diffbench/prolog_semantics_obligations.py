#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Fail closed when the audited Prolog-semantics ledger becomes stale."""

from __future__ import annotations

import csv
import hashlib
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "diffbench" / "prolog-semantics-obligations.tsv"
AXIOM_AUDIT = ROOT / "PLeaTTa" / "Proofs" / "AxiomAudit.lean"
TRACE_SEMANTICS = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologTraceSemantics.lean"
TERM_ALGEBRA = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologTermAlgebra.lean"
PROLOG_FLOAT = ROOT / "PLeaTTa" / "PrologFloat.lean"
UNIFICATION_CORE = ROOT / "MettaHyperonFull" / "Core" / "Unification.lean"
PETTA_UNIFICATION = ROOT / "PLeaTTa" / "PeTTaUnification.lean"
UNIFICATION_PROOFS = ROOT / "PLeaTTa" / "Proofs" / "Unification.lean"
PERSISTENT_SUBST = ROOT / "PLeaTTa" / "PersistentSubst.lean"
ORDERED_MGU = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologMgu.lean"
LOCAL_RESOLVER = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologResolver.lean"
DATABASE_ACTIONS = (
    ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologDatabaseActions.lean"
)
PROLOG_COPY = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologCopy.lean"
GOAL_SEMANTICS = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologGoalSemantics.lean"
MACHINE = ROOT / "PLeaTTa" / "Machine.lean"
DEMAND_DRIVEN_STEP = ROOT / "PLeaTTa" / "Proofs" / "DemandDrivenStep.lean"
FINDALL_COPY = ROOT / "PLeaTTa" / "Proofs" / "FindallCopy.lean"
PROLOG_FINDALL_COPY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologFindallCopyBridge.lean"
)
PROLOG_FINDALL_RESIDUAL_VARIANT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallResidualVariantBridge.lean"
)
DEMAND_DRIVEN_CALL_STEP = (
    ROOT / "PLeaTTa" / "Proofs" / "DemandDrivenCallStep.lean"
)
PROLOG_STATE_BRIDGE = ROOT / "PLeaTTa" / "Proofs" / "PrologStateBridge.lean"
PROLOG_FINDALL_ENTRY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologFindallEntryBridge.lean"
)
PROLOG_FINDALL_FRAME_ZIPPER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallFrameZipperBridge.lean"
)
PROLOG_ACTIVE_CONTROL_CONTEXT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologActiveControlContextBridge.lean"
)
PROLOG_FINDALL_DISJUNCTION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallDisjunctionBridge.lean"
)
PROLOG_FINDALL_CLOSED_BANK_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallClosedBankBridge.lean"
)
PROLOG_FINDALL_CLOSED_BANK_UNIFY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallClosedBankUnifyBridge.lean"
)
PROLOG_FINDALL_DISJUNCTION_EXIT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallDisjunctionExitBridge.lean"
)
PROLOG_FINDALL_EXIT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologFindallExitBridge.lean"
)
PROLOG_FINDALL_EXIT_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallExitPayloadBridge.lean"
)
PROLOG_FINDALL_VARIANT_EXIT_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallVariantExitPayloadBridge.lean"
)
PROLOG_FINDALL_BAG_ALPHA_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallBagAlphaBridge.lean"
)
PROLOG_RESIDUAL_FOREST_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologResidualForestBridge.lean"
)
PROLOG_GOAL_TERM_FOREST_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologGoalTermForestBridge.lean"
)
PROLOG_GOAL_CONTROL_CARRY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologGoalControlCarryBridge.lean"
)
PROLOG_FINDALL_TAIL_FOREST_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologFindallTailForestBridge.lean"
)
PROLOG_ANSWER_ORIGIN_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologAnswerOriginBridge.lean"
)
PROLOG_ANSWER_RESOURCE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologAnswerResourceBridge.lean"
)
PROLOG_FINDALL_ANSWER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallAnswerBridge.lean"
)
PROLOG_FINDALL_ANSWER_RESOURCE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallAnswerResourceBridge.lean"
)
PROLOG_ANSWER_PULL_CLASSIFICATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologAnswerPullClassificationBridge.lean"
)
PROLOG_FINDALL_ANSWER_EXIT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallAnswerExitBridge.lean"
)
PROLOG_ANSWER_SOURCE_CATCHUP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologAnswerSourceCatchupBridge.lean"
)
PROLOG_ANSWER_SELECTED_HEAD_OFFSET_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologAnswerSelectedHeadOffsetBridge.lean"
)
PROLOG_FINDALL_LOCAL_LIVE_CATCHUP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFindallLocalLiveCatchupBridge.lean"
)
PROLOG_ALPHA_FRESH_FRONTIER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologAlphaFreshFrontierBridge.lean"
)
PROLOG_CALL_ENTRY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologCallEntryBridge.lean"
)
PROLOG_CALL_STEP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologCallStepBridge.lean"
)
PROLOG_PREFILTER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologPrefilterBridge.lean"
)
PROLOG_PREFILTER_SCAN_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologPrefilterScanBridge.lean"
)
PROLOG_CALL_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologCallPayloadBridge.lean"
)
PROLOG_PREFILTER_CALL_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologPrefilterCallBridge.lean"
)
PROLOG_CURSOR_ALTERNATIVE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCursorAlternativeBridge.lean"
)
PROLOG_SUPPORTED_CURSOR_ALTERNATIVE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologSupportedCursorAlternativeBridge.lean"
)
PROLOG_SUPPORTED_CALL_FRONTIER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologSupportedCallFrontierBridge.lean"
)
PROLOG_MGU_BRIDGE = ROOT / "PLeaTTa" / "Proofs" / "PrologMguBridge.lean"
PROLOG_MGU_VALUATION = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologMguValuation.lean"
)
PROLOG_MGU_OPEN_AGREEMENT = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologMguOpenAgreement.lean"
)
PROLOG_MGU_TOPOLOGY = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologMguTopology.lean"
)
PROLOG_MGU_EXECUTABLE_OPEN_FACTOR = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologMguExecutableOpenFactor.lean"
)
PROLOG_MGU_DIRECT_SIMULATION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologMguDirectSimulation.lean"
)
PROLOG_MGU_VARIANT = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologMguVariant.lean"
)
PROLOG_MGU_VARIANT_RENAMING = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologMguVariantRenaming.lean"
)
PROLOG_GOAL_MGU_VARIANT = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologGoalMguVariant.lean"
)
PROLOG_MGU_COMPOSITION = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologMguComposition.lean"
)
PROLOG_CANONICAL_MGU_SIMULATION = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologCanonicalMguSimulation.lean"
)
PROLOG_SEQUENTIAL_MGU = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologSequentialMgu.lean"
)
PROLOG_RUNTIME_DECODE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologRuntimeDecode.lean"
)
PROLOG_RETRACT_ENCODING_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologRetractEncodingBridge.lean"
)
PROLOG_ACTIVATION_UNIFIER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologActivationUnifierBridge.lean"
)
PROLOG_ORDINARY_STEP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologOrdinaryStepBridge.lean"
)
PROLOG_DISJUNCTION_STEP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologDisjunctionStepBridge.lean"
)
PROLOG_DATABASE_ACTION_STEP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologDatabaseActionStepBridge.lean"
)
PROLOG_SEGMENTED_PRODUCT_STEP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologSegmentedProductStepBridge.lean"
)
PROLOG_RECURSIVE_CALL_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRecursiveCallPayloadBridge.lean"
)
PROLOG_REPRESENTATIVE_CALL_PREFILTER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRepresentativeCallPrefilterBridge.lean"
)
PROLOG_REPRESENTATIVE_CALL_FRONTIER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRepresentativeCallFrontierBridge.lean"
)
PROLOG_REPRESENTATIVE_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRepresentativeActivationBridge.lean"
)
PROLOG_REPRESENTATIVE_TASK_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRepresentativeTaskActivationBridge.lean"
)
PROLOG_REPRESENTATIVE_STEP_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRepresentativeStepActivationBridge.lean"
)
PROLOG_TASK_CONTINUATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologTaskContinuationBridge.lean"
)
PROLOG_CONTROL_SEGMENT_SPINE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologControlSegmentSpineBridge.lean"
)
PROLOG_REPRESENTATIVE_PRODUCT_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRepresentativeProductActivationBridge.lean"
)
PROLOG_RETAINED_CURSOR_OWNERSHIP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRetainedCursorOwnershipBridge.lean"
)
PROLOG_ACTIVATED_PRODUCT_STEP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologActivatedProductStepBridge.lean"
)
PROLOG_PRODUCT_SCHEDULING_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologProductSchedulingBridge.lean"
)
PROLOG_SOURCE_PRODUCT_CONTEXT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologSourceProductContextBridge.lean"
)
PROLOG_SPINED_SOURCE_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologSpinedSourceActivationBridge.lean"
)
PROLOG_PRODUCT_RESOURCE_CONTEXT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologProductResourceContextBridge.lean"
)
PROLOG_PRODUCT_RESOURCE_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologProductResourceTransitionBridge.lean"
)
PROLOG_PRODUCT_ACTIVE_CONTROL_EMBEDDING_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologProductActiveControlEmbeddingBridge.lean"
)
PROLOG_COLLECTION_BOUNDED_PRODUCT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCollectionBoundedProductBridge.lean"
)
PROLOG_NESTED_CALL_ENTRY_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologNestedCallEntryPayloadBridge.lean"
)
PROLOG_NESTED_CALL_CHAIN_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologNestedCallChainBridge.lean"
)
PROLOG_NESTED_CALL_READY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologNestedCallReadyBridge.lean"
)
PROLOG_ROOT_CALL_READY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRootCallReadyBridge.lean"
)
PROLOG_NESTED_CALL_PREFIX_INDUCTION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologNestedCallPrefixInductionBridge.lean"
)
PROLOG_NESTED_CALL_READY_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologNestedCallReadyRegression.lean"
)
PROLOG_UNBOUND_NESTED_CALL_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologUnboundNestedCallRegression.lean"
)
PROLOG_ROOT_SCHEDULED_SELECTION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRootScheduledSelectionBridge.lean"
)
PROLOG_HETEROGENEOUS_PREFIX_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologHeterogeneousPrefixBridge.lean"
)
PROLOG_HETEROGENEOUS_PREFIX_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologHeterogeneousPrefixRegression.lean"
)
PROLOG_ROOT_REJECTED_PREFIX_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRootRejectedPrefixRegression.lean"
)
PROLOG_RETAINED_PAYLOAD_SNAPSHOT_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRetainedPayloadSnapshotBridge.lean"
)
PROLOG_RETAINED_PAYLOAD_CATCHUP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRetainedPayloadCatchupBridge.lean"
)
PROLOG_RETAINED_PAYLOAD_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRetainedPayloadActivationBridge.lean"
)
PROLOG_NESTED_RETAINED_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologNestedRetainedPayloadBridge.lean"
)
PROLOG_CURRENT_SESSION_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionPayloadBridge.lean"
)
PROLOG_CURRENT_SESSION_PAYLOAD_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionPayloadTransitionBridge.lean"
)
PROLOG_PERSISTENT_FREE_ACTIVE_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologPersistentFreeActivePayloadBridge.lean"
)
PROLOG_PERSISTENT_FREE_SCHEDULED_PAYLOAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologPersistentFreeScheduledPayloadBridge.lean"
)
PROLOG_SCHEDULED_ANSWER_PROPAGATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledAnswerPropagationBridge.lean"
)
PROLOG_SCHEDULED_HISTORY_BUILD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledHistoryBuildBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_RESUME_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadResumeBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_RESUME_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadResumeRegression.lean"
)
PROLOG_SCHEDULED_PAYLOAD_PATH_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadPathBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_PATH_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadPathRegression.lean"
)
PROLOG_SCHEDULED_PAYLOAD_LANDING_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadLandingBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_LANDING_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadLandingRegression.lean"
)
PROLOG_SCHEDULED_PAYLOAD_POST_HEAD_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadPostHeadBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_POST_HEAD_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadPostHeadRegression.lean"
)
PROLOG_SCHEDULED_PAYLOAD_OPEN_CONF_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadOpenConfBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_OPEN_CONF_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadOpenConfRegression.lean"
)
PROLOG_SCHEDULED_PAYLOAD_REJECTION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadRejectionBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_REJECTION_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadRejectionRegression.lean"
)
PROLOG_SCHEDULED_PAYLOAD_SUCCESS_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadSuccessBridge.lean"
)
PROLOG_SCHEDULED_PAYLOAD_SUCCESS_CARRIER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadSuccessCarrierBridge.lean"
)
PROLOG_SCHEDULED_SUCCESS_PREFIX_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledSuccessPrefixBridge.lean"
)
PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_PULL_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologPersistentFreeScheduledRejectionPullBridge.lean"
)
PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_PULL_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologPersistentFreeScheduledRejectionPullRegression.lean"
)
PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_CATCHUP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologPersistentFreeScheduledRejectionCatchupBridge.lean"
)
PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_CATCHUP_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologPersistentFreeScheduledRejectionCatchupRegression.lean"
)
PROLOG_SCHEDULED_REJECTION_REACHABILITY_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledRejectionReachabilityRegression.lean"
)
PROLOG_SCHEDULED_PAYLOAD_SUCCESS_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledPayloadSuccessRegression.lean"
)
PROLOG_ROOT_CLOSED_ANSWER_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRootClosedAnswerBridge.lean"
)
PROLOG_ROOT_CLOSED_LOCAL_LIVE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRootClosedLocalLiveBridge.lean"
)
PROLOG_ROOT_CLOSED_LOCAL_LIVE_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologRootClosedLocalLiveRegression.lean"
)
PROLOG_ANSWER_VALUE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologAnswerValueBridge.lean"
)
PROLOG_SCHEDULED_ANSWER_VALUE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologScheduledAnswerValueBridge.lean"
)
PROLOG_ANSWER_VISIBILITY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologAnswerVisibilityBridge.lean"
)
PROLOG_UNBOUND_PUBLIC_ANSWER_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologUnboundPublicAnswerRegression.lean"
)
PROLOG_CURRENT_SESSION_ASSERTION_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionAssertionTransitionBridge.lean"
)
PROLOG_CURRENT_SESSION_UNIFY_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionUnifyTransitionBridge.lean"
)
RESOLUTION_COUNTER = (
    ROOT / "PLeaTTa" / "Proofs" / "ResolutionCounter.lean"
)
PROLOG_RETRACT_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologRetractRegression.lean"
)
PROLOG_CURRENT_SESSION_ADMINISTRATIVE_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionAdministrativeTransitionBridge.lean"
)
PROLOG_CURRENT_SESSION_FAILURE_PAYLOAD_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionFailurePayloadTransitionBridge.lean"
)
PROLOG_CURRENT_SESSION_POST_FAILURE_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionPostFailureActivationBridge.lean"
)
PROLOG_FAILURE_REBASE_PREFIX_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFailureRebasePrefixBridge.lean"
)
PROLOG_RESOLVER_READINESS_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologResolverReadinessBridge.lean"
)
PROLOG_FAILURE_REBASE_REGRESSION = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologFailureRebaseRegression.lean"
)
PROLOG_CURRENT_SESSION_EXHAUSTED_PAYLOAD_CATCHUP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionExhaustedPayloadCatchupBridge.lean"
)
PROLOG_CURRENT_SESSION_ASSERTION_FAILURE_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCurrentSessionAssertionFailureTransitionBridge.lean"
)
PROLOG_ACTIVATION_FAILURE_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologActivationFailureBridge.lean"
)
PROLOG_HEAD_FAILURE_CONTINUATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologHeadFailureContinuationBridge.lean"
)
PROLOG_BODY_FAILURE_BACKTRACKING_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologBodyFailureBacktrackingBridge.lean"
)
PROLOG_BODY_FAILURE_RESOURCE_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologBodyFailureResourceTransitionBridge.lean"
)
PROLOG_BODY_FAILURE_EXHAUSTED_RESOURCE_TRANSITION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologBodyFailureExhaustedResourceTransitionBridge.lean"
)
PROLOG_BODY_FAILURE_OUTER_RESOURCE_CATCHUP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologBodyFailureOuterResourceCatchupBridge.lean"
)
PROLOG_BODY_FAILURE_OUTER_RESOURCE_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologBodyFailureOuterResourceActivationBridge.lean"
)
PROLOG_CANONICAL_RUNTIME_READING = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologCanonicalRuntimeReading.lean"
)
PROLOG_BOOLEAN_ALIAS_SAFETY = (
    ROOT / "PLeaTTa" / "Proofs" /
    "PrologBooleanAliasSafety.lean"
)
PROLOG_GOAL_ALPHA = ROOT / "PLeaTTa" / "Proofs" / "PrologGoalAlpha.lean"
PROLOG_ACTIVATION_MACRO = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologActivationMacro.lean"
)
PROLOG_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologActivationBridge.lean"
)
PINNED_PETTA_REVISION = "6b7f52f064bdbc82fabd0a0998404121fb01d52e"
FIELDS = ["id", "native_source", "layer", "reference", "proof", "status", "finding"]
LAYERS = {"trace", "control", "collection", "exception", "world", "boundary",
          "resolver", "projection", "composition", "instantiation"}
PROOFS = {"SC", "W", "SH", "N"}
STATUSES = {"PASS", "FAIL", "GAP", "BOUNDARY"}
REQUIRED_PREFIXES = {
    "TRACE.", "CONTROL.", "CUT.", "COLLECT.", "EXCEPTION.", "WORLD.",
    "CALL.", "RESOLVER.", "EXTERNAL.", "PROJECTION.", "BISIM.",
    "COMPOSE.", "PETTACLAW.",
}

# The legacy reference column also contains descriptive vocabulary and
# wildcard families, so it cannot yet be interpreted uniformly as Lean
# declaration names.  New rows opt into exact checking here until that legacy
# metadata is normalized.  A listed row must be PASS and every semicolon-
# separated reference must be an actual `#print axioms` target.
STRICT_AXIOM_AUDIT_ROWS = {
    "BISIM.database_assertion_steps",
    "BISIM.scheduled_success_global_prefix",
    "BISIM.catch_macro_prefix",
    "BISIM.softcut_macro_prefix",
    "BISIM.root_closed_answer_pull",
    "BISIM.root_closed_local_live_answer",
    "BISIM.scheduled_payload_landing",
    "BISIM.scheduled_payload_rejected_head",
    "BISIM.scheduled_payload_successful_head",
    "BISIM.scheduled_phase_packet_free",
    "BISIM.root_closed_public_answer_value",
    "BISIM.answer_visibility_public",
    "BISIM.findall_collection_answer_general",
    "BISIM.findall_bag_alpha_support",
    "BISIM.findall_tail_control_materialization",
    "WORLD.retract_unifier_reflection",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def axiom_audit_targets() -> set[str]:
    return set(re.findall(
        r"^#print axioms\s+([^\s]+)",
        AXIOM_AUDIT.read_text(encoding="utf-8"),
        flags=re.MULTILINE,
    ))


def packet_free_scheduled_consumer_errors() -> list[str]:
    """Pin the exact legacy scheduled compatibility surface.

    All PLeaTTa Lean sources are checked, not only the Prolog proof glob.
    Axiom-audit directives may name compatibility declarations, but executable
    declarations and proofs may use the legacy carrier only at the exact
    definition/adapter occurrences already present in the compatibility
    module.  Exact occurrence counts also reject an alias added inside that
    module and consumed elsewhere.
    """
    errors: list[str] = []
    legacy_patterns = (
        ("legacy scheduled carrier", re.compile(
            r"(?<!Free)ScheduledPayloadState")),
        ("scheduled one-way adapter", re.compile(
            r"PersistentFreeScheduledPayloadState\.ofLegacy")),
    )
    # These are a reviewed compatibility budget, not values to update merely
    # because this gate turns red: increasing either count expands the legacy
    # surface and requires an explicit adequacy review.
    allowed_counts = {
        PROLOG_HETEROGENEOUS_PREFIX_BRIDGE: (32, 2),
    }
    for path in sorted((ROOT / "PLeaTTa").rglob("*.lean")):
        text = "\n".join(
            line for line in path.read_text(encoding="utf-8").splitlines()
            if not line.lstrip().startswith("#print axioms")
        )
        actual = tuple(len(pattern.findall(text))
                       for _label, pattern in legacy_patterns)
        expected = allowed_counts.get(path, (0, 0))
        if actual != expected:
            relative = path.relative_to(ROOT)
            detail = ", ".join(
                f"{label}={count} (expected {wanted})"
                for (label, _pattern), count, wanted
                in zip(legacy_patterns, actual, expected)
                if count != wanted
            )
            errors.append(f"{relative}: {detail}")
    return errors


def load_ledger() -> tuple[dict[str, str], list[dict[str, str]]]:
    metadata: dict[str, str] = {}
    table: list[str] = []
    for raw in LEDGER.read_text(encoding="utf-8").splitlines():
        if raw.startswith("#"):
            body = raw[1:].strip()
            if "=" in body:
                key, value = body.split("=", 1)
                metadata[key.strip()] = value.strip()
        elif raw.strip():
            table.append(raw)
    if not table:
        raise ValueError("ledger has no table")
    reader = csv.DictReader(table, delimiter="\t")
    if reader.fieldnames != FIELDS:
        raise ValueError(f"unexpected columns: {reader.fieldnames!r}")
    return metadata, list(reader)


def check() -> list[str]:
    errors: list[str] = []
    try:
        metadata, rows = load_ledger()
    except (OSError, ValueError) as exc:
        return [str(exc)]

    expected_metadata = {
        "pinned_petta_revision": PINNED_PETTA_REVISION,
        "trace_semantics_sha256": digest(TRACE_SEMANTICS),
        "term_algebra_sha256": digest(TERM_ALGEBRA),
        "prolog_float_sha256": digest(PROLOG_FLOAT),
        "unification_core_sha256": digest(UNIFICATION_CORE),
        "petta_unification_sha256": digest(PETTA_UNIFICATION),
        "unification_proofs_sha256": digest(UNIFICATION_PROOFS),
        "persistent_subst_sha256": digest(PERSISTENT_SUBST),
        "ordered_mgu_sha256": digest(ORDERED_MGU),
        "local_resolver_sha256": digest(LOCAL_RESOLVER),
        "database_actions_sha256": digest(DATABASE_ACTIONS),
        "prolog_copy_sha256": digest(PROLOG_COPY),
        "goal_semantics_sha256": digest(GOAL_SEMANTICS),
        "machine_sha256": digest(MACHINE),
        "demand_driven_step_sha256": digest(DEMAND_DRIVEN_STEP),
        "findall_copy_sha256": digest(FINDALL_COPY),
        "prolog_findall_copy_bridge_sha256":
            digest(PROLOG_FINDALL_COPY_BRIDGE),
        "prolog_findall_residual_variant_bridge_sha256":
            digest(PROLOG_FINDALL_RESIDUAL_VARIANT_BRIDGE),
        "demand_driven_call_step_sha256": digest(DEMAND_DRIVEN_CALL_STEP),
        "prolog_state_bridge_sha256": digest(PROLOG_STATE_BRIDGE),
        "prolog_findall_entry_bridge_sha256":
            digest(PROLOG_FINDALL_ENTRY_BRIDGE),
        "prolog_findall_frame_zipper_bridge_sha256":
            digest(PROLOG_FINDALL_FRAME_ZIPPER_BRIDGE),
        "prolog_active_control_context_bridge_sha256":
            digest(PROLOG_ACTIVE_CONTROL_CONTEXT_BRIDGE),
        "prolog_findall_disjunction_bridge_sha256":
            digest(PROLOG_FINDALL_DISJUNCTION_BRIDGE),
        "prolog_findall_closed_bank_bridge_sha256":
            digest(PROLOG_FINDALL_CLOSED_BANK_BRIDGE),
        "prolog_findall_closed_bank_unify_bridge_sha256":
            digest(PROLOG_FINDALL_CLOSED_BANK_UNIFY_BRIDGE),
        "prolog_findall_disjunction_exit_bridge_sha256":
            digest(PROLOG_FINDALL_DISJUNCTION_EXIT_BRIDGE),
        "prolog_findall_exit_bridge_sha256":
            digest(PROLOG_FINDALL_EXIT_BRIDGE),
        "prolog_findall_exit_payload_bridge_sha256":
            digest(PROLOG_FINDALL_EXIT_PAYLOAD_BRIDGE),
        "prolog_findall_variant_exit_payload_bridge_sha256":
            digest(PROLOG_FINDALL_VARIANT_EXIT_PAYLOAD_BRIDGE),
        "prolog_findall_bag_alpha_bridge_sha256":
            digest(PROLOG_FINDALL_BAG_ALPHA_BRIDGE),
        "prolog_residual_forest_bridge_sha256":
            digest(PROLOG_RESIDUAL_FOREST_BRIDGE),
        "prolog_goal_term_forest_bridge_sha256":
            digest(PROLOG_GOAL_TERM_FOREST_BRIDGE),
        "prolog_goal_control_carry_bridge_sha256":
            digest(PROLOG_GOAL_CONTROL_CARRY_BRIDGE),
        "prolog_findall_tail_forest_bridge_sha256":
            digest(PROLOG_FINDALL_TAIL_FOREST_BRIDGE),
        "prolog_answer_origin_bridge_sha256":
            digest(PROLOG_ANSWER_ORIGIN_BRIDGE),
        "prolog_answer_resource_bridge_sha256":
            digest(PROLOG_ANSWER_RESOURCE_BRIDGE),
        "prolog_findall_answer_bridge_sha256":
            digest(PROLOG_FINDALL_ANSWER_BRIDGE),
        "prolog_findall_answer_resource_bridge_sha256":
            digest(PROLOG_FINDALL_ANSWER_RESOURCE_BRIDGE),
        "prolog_answer_pull_classification_bridge_sha256":
            digest(PROLOG_ANSWER_PULL_CLASSIFICATION_BRIDGE),
        "prolog_findall_answer_exit_bridge_sha256":
            digest(PROLOG_FINDALL_ANSWER_EXIT_BRIDGE),
        "prolog_answer_source_catchup_bridge_sha256":
            digest(PROLOG_ANSWER_SOURCE_CATCHUP_BRIDGE),
        "prolog_answer_selected_head_offset_bridge_sha256":
            digest(PROLOG_ANSWER_SELECTED_HEAD_OFFSET_BRIDGE),
        "prolog_findall_local_live_catchup_bridge_sha256":
            digest(PROLOG_FINDALL_LOCAL_LIVE_CATCHUP_BRIDGE),
        "prolog_alpha_fresh_frontier_bridge_sha256":
            digest(PROLOG_ALPHA_FRESH_FRONTIER_BRIDGE),
        "prolog_call_entry_bridge_sha256": digest(PROLOG_CALL_ENTRY_BRIDGE),
        "prolog_call_step_bridge_sha256": digest(PROLOG_CALL_STEP_BRIDGE),
        "prolog_prefilter_bridge_sha256": digest(PROLOG_PREFILTER_BRIDGE),
        "prolog_prefilter_scan_bridge_sha256":
            digest(PROLOG_PREFILTER_SCAN_BRIDGE),
        "prolog_call_payload_bridge_sha256":
            digest(PROLOG_CALL_PAYLOAD_BRIDGE),
        "prolog_prefilter_call_bridge_sha256":
            digest(PROLOG_PREFILTER_CALL_BRIDGE),
        "prolog_cursor_alternative_bridge_sha256":
            digest(PROLOG_CURSOR_ALTERNATIVE_BRIDGE),
        "prolog_supported_cursor_alternative_bridge_sha256":
            digest(PROLOG_SUPPORTED_CURSOR_ALTERNATIVE_BRIDGE),
        "prolog_supported_call_frontier_bridge_sha256":
            digest(PROLOG_SUPPORTED_CALL_FRONTIER_BRIDGE),
        "prolog_mgu_bridge_sha256": digest(PROLOG_MGU_BRIDGE),
        "prolog_mgu_valuation_sha256": digest(PROLOG_MGU_VALUATION),
        "prolog_mgu_open_agreement_sha256":
            digest(PROLOG_MGU_OPEN_AGREEMENT),
        "prolog_mgu_topology_sha256": digest(PROLOG_MGU_TOPOLOGY),
        "prolog_mgu_executable_open_factor_sha256":
            digest(PROLOG_MGU_EXECUTABLE_OPEN_FACTOR),
        "prolog_mgu_direct_simulation_sha256":
            digest(PROLOG_MGU_DIRECT_SIMULATION),
        "prolog_mgu_variant_sha256": digest(PROLOG_MGU_VARIANT),
        "prolog_mgu_variant_renaming_sha256":
            digest(PROLOG_MGU_VARIANT_RENAMING),
        "prolog_goal_mgu_variant_sha256":
            digest(PROLOG_GOAL_MGU_VARIANT),
        "prolog_mgu_composition_sha256":
            digest(PROLOG_MGU_COMPOSITION),
        "prolog_canonical_mgu_simulation_sha256":
            digest(PROLOG_CANONICAL_MGU_SIMULATION),
        "prolog_sequential_mgu_sha256":
            digest(PROLOG_SEQUENTIAL_MGU),
        "prolog_runtime_decode_sha256":
            digest(PROLOG_RUNTIME_DECODE),
        "prolog_retract_encoding_bridge_sha256":
            digest(PROLOG_RETRACT_ENCODING_BRIDGE),
        "prolog_activation_unifier_bridge_sha256":
            digest(PROLOG_ACTIVATION_UNIFIER_BRIDGE),
        "prolog_ordinary_step_bridge_sha256":
            digest(PROLOG_ORDINARY_STEP_BRIDGE),
        "prolog_disjunction_step_bridge_sha256":
            digest(PROLOG_DISJUNCTION_STEP_BRIDGE),
        "prolog_database_action_step_bridge_sha256":
            digest(PROLOG_DATABASE_ACTION_STEP_BRIDGE),
        "prolog_segmented_product_step_bridge_sha256":
            digest(PROLOG_SEGMENTED_PRODUCT_STEP_BRIDGE),
        "prolog_recursive_call_payload_bridge_sha256":
            digest(PROLOG_RECURSIVE_CALL_PAYLOAD_BRIDGE),
        "prolog_representative_call_prefilter_bridge_sha256":
            digest(PROLOG_REPRESENTATIVE_CALL_PREFILTER_BRIDGE),
        "prolog_representative_call_frontier_bridge_sha256":
            digest(PROLOG_REPRESENTATIVE_CALL_FRONTIER_BRIDGE),
        "prolog_representative_activation_bridge_sha256":
            digest(PROLOG_REPRESENTATIVE_ACTIVATION_BRIDGE),
        "prolog_representative_task_activation_bridge_sha256":
            digest(PROLOG_REPRESENTATIVE_TASK_ACTIVATION_BRIDGE),
        "prolog_representative_step_activation_bridge_sha256":
            digest(PROLOG_REPRESENTATIVE_STEP_ACTIVATION_BRIDGE),
        "prolog_task_continuation_bridge_sha256":
            digest(PROLOG_TASK_CONTINUATION_BRIDGE),
        "prolog_control_segment_spine_bridge_sha256":
            digest(PROLOG_CONTROL_SEGMENT_SPINE_BRIDGE),
        "prolog_representative_product_activation_bridge_sha256":
            digest(PROLOG_REPRESENTATIVE_PRODUCT_ACTIVATION_BRIDGE),
        "prolog_retained_cursor_ownership_bridge_sha256":
            digest(PROLOG_RETAINED_CURSOR_OWNERSHIP_BRIDGE),
        "prolog_activated_product_step_bridge_sha256":
            digest(PROLOG_ACTIVATED_PRODUCT_STEP_BRIDGE),
        "prolog_product_scheduling_bridge_sha256":
            digest(PROLOG_PRODUCT_SCHEDULING_BRIDGE),
        "prolog_source_product_context_bridge_sha256":
            digest(PROLOG_SOURCE_PRODUCT_CONTEXT_BRIDGE),
        "prolog_spined_source_activation_bridge_sha256":
            digest(PROLOG_SPINED_SOURCE_ACTIVATION_BRIDGE),
        "prolog_product_resource_context_bridge_sha256":
            digest(PROLOG_PRODUCT_RESOURCE_CONTEXT_BRIDGE),
        "prolog_product_resource_transition_bridge_sha256":
            digest(PROLOG_PRODUCT_RESOURCE_TRANSITION_BRIDGE),
        "prolog_product_active_control_embedding_bridge_sha256":
            digest(PROLOG_PRODUCT_ACTIVE_CONTROL_EMBEDDING_BRIDGE),
        "prolog_collection_bounded_product_bridge_sha256":
            digest(PROLOG_COLLECTION_BOUNDED_PRODUCT_BRIDGE),
        "prolog_nested_call_entry_payload_bridge_sha256":
            digest(PROLOG_NESTED_CALL_ENTRY_PAYLOAD_BRIDGE),
        "prolog_nested_call_chain_bridge_sha256":
            digest(PROLOG_NESTED_CALL_CHAIN_BRIDGE),
        "prolog_nested_call_ready_bridge_sha256":
            digest(PROLOG_NESTED_CALL_READY_BRIDGE),
        "prolog_root_call_ready_bridge_sha256":
            digest(PROLOG_ROOT_CALL_READY_BRIDGE),
        "prolog_nested_call_prefix_induction_bridge_sha256":
            digest(PROLOG_NESTED_CALL_PREFIX_INDUCTION_BRIDGE),
        "prolog_nested_call_ready_regression_sha256":
            digest(PROLOG_NESTED_CALL_READY_REGRESSION),
        "prolog_unbound_nested_call_regression_sha256":
            digest(PROLOG_UNBOUND_NESTED_CALL_REGRESSION),
        "prolog_root_scheduled_selection_bridge_sha256":
            digest(PROLOG_ROOT_SCHEDULED_SELECTION_BRIDGE),
        "prolog_heterogeneous_prefix_bridge_sha256":
            digest(PROLOG_HETEROGENEOUS_PREFIX_BRIDGE),
        "prolog_heterogeneous_prefix_regression_sha256":
            digest(PROLOG_HETEROGENEOUS_PREFIX_REGRESSION),
        "prolog_root_rejected_prefix_regression_sha256":
            digest(PROLOG_ROOT_REJECTED_PREFIX_REGRESSION),
        "prolog_retained_payload_snapshot_bridge_sha256":
            digest(PROLOG_RETAINED_PAYLOAD_SNAPSHOT_BRIDGE),
        "prolog_retained_payload_catchup_bridge_sha256":
            digest(PROLOG_RETAINED_PAYLOAD_CATCHUP_BRIDGE),
        "prolog_retained_payload_activation_bridge_sha256":
            digest(PROLOG_RETAINED_PAYLOAD_ACTIVATION_BRIDGE),
        "prolog_nested_retained_payload_bridge_sha256":
            digest(PROLOG_NESTED_RETAINED_PAYLOAD_BRIDGE),
        "prolog_current_session_payload_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_PAYLOAD_BRIDGE),
        "prolog_current_session_payload_transition_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_PAYLOAD_TRANSITION_BRIDGE),
        "prolog_persistent_free_active_payload_bridge_sha256":
            digest(PROLOG_PERSISTENT_FREE_ACTIVE_PAYLOAD_BRIDGE),
        "prolog_persistent_free_scheduled_payload_bridge_sha256":
            digest(PROLOG_PERSISTENT_FREE_SCHEDULED_PAYLOAD_BRIDGE),
        "prolog_scheduled_answer_propagation_bridge_sha256":
            digest(PROLOG_SCHEDULED_ANSWER_PROPAGATION_BRIDGE),
        "prolog_scheduled_history_build_bridge_sha256":
            digest(PROLOG_SCHEDULED_HISTORY_BUILD_BRIDGE),
        "prolog_scheduled_payload_resume_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_RESUME_BRIDGE),
        "prolog_scheduled_payload_resume_regression_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_RESUME_REGRESSION),
        "prolog_scheduled_payload_path_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_PATH_BRIDGE),
        "prolog_scheduled_payload_path_regression_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_PATH_REGRESSION),
        "prolog_scheduled_payload_landing_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_LANDING_BRIDGE),
        "prolog_scheduled_payload_landing_regression_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_LANDING_REGRESSION),
        "prolog_scheduled_payload_post_head_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_POST_HEAD_BRIDGE),
        "prolog_scheduled_payload_post_head_regression_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_POST_HEAD_REGRESSION),
        "prolog_scheduled_payload_open_conf_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_OPEN_CONF_BRIDGE),
        "prolog_scheduled_payload_open_conf_regression_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_OPEN_CONF_REGRESSION),
        "prolog_scheduled_payload_rejection_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_REJECTION_BRIDGE),
        "prolog_scheduled_payload_rejection_regression_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_REJECTION_REGRESSION),
        "prolog_scheduled_payload_success_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_SUCCESS_BRIDGE),
        "prolog_scheduled_payload_success_carrier_bridge_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_SUCCESS_CARRIER_BRIDGE),
        "prolog_scheduled_success_prefix_bridge_sha256":
            digest(PROLOG_SCHEDULED_SUCCESS_PREFIX_BRIDGE),
        "prolog_persistent_free_scheduled_rejection_pull_bridge_sha256":
            digest(PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_PULL_BRIDGE),
        "prolog_persistent_free_scheduled_rejection_pull_regression_sha256":
            digest(PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_PULL_REGRESSION),
        "prolog_persistent_free_scheduled_rejection_catchup_bridge_sha256":
            digest(PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_CATCHUP_BRIDGE),
        "prolog_persistent_free_scheduled_rejection_catchup_regression_sha256":
            digest(
                PROLOG_PERSISTENT_FREE_SCHEDULED_REJECTION_CATCHUP_REGRESSION
            ),
        "prolog_scheduled_rejection_reachability_regression_sha256":
            digest(PROLOG_SCHEDULED_REJECTION_REACHABILITY_REGRESSION),
        "prolog_scheduled_payload_success_regression_sha256":
            digest(PROLOG_SCHEDULED_PAYLOAD_SUCCESS_REGRESSION),
        "prolog_root_closed_answer_bridge_sha256":
            digest(PROLOG_ROOT_CLOSED_ANSWER_BRIDGE),
        "prolog_root_closed_local_live_bridge_sha256":
            digest(PROLOG_ROOT_CLOSED_LOCAL_LIVE_BRIDGE),
        "prolog_root_closed_local_live_regression_sha256":
            digest(PROLOG_ROOT_CLOSED_LOCAL_LIVE_REGRESSION),
        "prolog_answer_value_bridge_sha256":
            digest(PROLOG_ANSWER_VALUE_BRIDGE),
        "prolog_scheduled_answer_value_bridge_sha256":
            digest(PROLOG_SCHEDULED_ANSWER_VALUE_BRIDGE),
        "prolog_answer_visibility_bridge_sha256":
            digest(PROLOG_ANSWER_VISIBILITY_BRIDGE),
        "prolog_unbound_public_answer_regression_sha256":
            digest(PROLOG_UNBOUND_PUBLIC_ANSWER_REGRESSION),
        "prolog_current_session_assertion_transition_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_ASSERTION_TRANSITION_BRIDGE),
        "prolog_current_session_unify_transition_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_UNIFY_TRANSITION_BRIDGE),
        "resolution_counter_sha256": digest(RESOLUTION_COUNTER),
        "prolog_retract_regression_sha256":
            digest(PROLOG_RETRACT_REGRESSION),
        "prolog_current_session_administrative_transition_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_ADMINISTRATIVE_TRANSITION_BRIDGE),
        "prolog_current_session_failure_payload_transition_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_FAILURE_PAYLOAD_TRANSITION_BRIDGE),
        "prolog_current_session_post_failure_activation_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_POST_FAILURE_ACTIVATION_BRIDGE),
        "prolog_failure_rebase_prefix_bridge_sha256":
            digest(PROLOG_FAILURE_REBASE_PREFIX_BRIDGE),
        "prolog_resolver_readiness_bridge_sha256":
            digest(PROLOG_RESOLVER_READINESS_BRIDGE),
        "prolog_failure_rebase_regression_sha256":
            digest(PROLOG_FAILURE_REBASE_REGRESSION),
        "prolog_current_session_exhausted_payload_catchup_bridge_sha256":
            digest(
                PROLOG_CURRENT_SESSION_EXHAUSTED_PAYLOAD_CATCHUP_BRIDGE
            ),
        "prolog_current_session_assertion_failure_transition_bridge_sha256":
            digest(PROLOG_CURRENT_SESSION_ASSERTION_FAILURE_TRANSITION_BRIDGE),
        "prolog_activation_failure_bridge_sha256":
            digest(PROLOG_ACTIVATION_FAILURE_BRIDGE),
        "prolog_head_failure_continuation_bridge_sha256":
            digest(PROLOG_HEAD_FAILURE_CONTINUATION_BRIDGE),
        "prolog_body_failure_backtracking_bridge_sha256":
            digest(PROLOG_BODY_FAILURE_BACKTRACKING_BRIDGE),
        "prolog_body_failure_resource_transition_bridge_sha256":
            digest(PROLOG_BODY_FAILURE_RESOURCE_TRANSITION_BRIDGE),
        "prolog_body_failure_exhausted_resource_transition_bridge_sha256":
            digest(PROLOG_BODY_FAILURE_EXHAUSTED_RESOURCE_TRANSITION_BRIDGE),
        "prolog_body_failure_outer_resource_catchup_bridge_sha256":
            digest(PROLOG_BODY_FAILURE_OUTER_RESOURCE_CATCHUP_BRIDGE),
        "prolog_body_failure_outer_resource_activation_bridge_sha256":
            digest(PROLOG_BODY_FAILURE_OUTER_RESOURCE_ACTIVATION_BRIDGE),
        "prolog_canonical_runtime_reading_sha256":
            digest(PROLOG_CANONICAL_RUNTIME_READING),
        "prolog_boolean_alias_safety_sha256":
            digest(PROLOG_BOOLEAN_ALIAS_SAFETY),
        "prolog_goal_alpha_sha256": digest(PROLOG_GOAL_ALPHA),
        "prolog_activation_macro_sha256": digest(PROLOG_ACTIVATION_MACRO),
        "prolog_activation_bridge_sha256": digest(PROLOG_ACTIVATION_BRIDGE),
    }
    expected_hash_keys = {
        key for key in expected_metadata if key.endswith("_sha256")
    }
    ledger_hash_keys = {
        key for key in metadata if key.endswith("_sha256")
    }
    untracked_hash_keys = sorted(ledger_hash_keys - expected_hash_keys)
    if untracked_hash_keys:
        errors.append(
            "ledger hash metadata has no audited path: "
            + ", ".join(untracked_hash_keys)
        )
    for key, expected in expected_metadata.items():
        actual = metadata.get(key)
        if actual != expected:
            errors.append(f"{key}: ledger={actual!r}, expected={expected!r}")

    if len(rows) < 30:
        errors.append(f"ledger unexpectedly small: {len(rows)} rows")

    seen: set[str] = set()
    for line, row in enumerate(rows, start=2):
        row_id = row["id"]
        if not row_id:
            errors.append(f"row {line}: empty id")
        elif row_id in seen:
            errors.append(f"row {line}: duplicate id {row_id}")
        seen.add(row_id)

        if row["layer"] not in LAYERS:
            errors.append(f"{row_id}: invalid layer {row['layer']!r}")
        if row["proof"] not in PROOFS:
            errors.append(f"{row_id}: invalid proof {row['proof']!r}")
        if row["status"] not in STATUSES:
            errors.append(f"{row_id}: invalid status {row['status']!r}")
        if not row["finding"]:
            errors.append(f"{row_id}: empty finding")

        if row["status"] == "PASS":
            if row["proof"] == "N":
                errors.append(f"{row_id}: PASS requires a checked proof or witness")
            if row["reference"] == "-":
                errors.append(f"{row_id}: PASS requires an independent reference")

    missing = sorted(
        prefix for prefix in REQUIRED_PREFIXES
        if not any(row_id.startswith(prefix) for row_id in seen)
    )
    if missing:
        errors.append("missing obligation families: " + ", ".join(missing))

    required_rows = {
        "EXTERNAL.imported_swi": "BOUNDARY",
        "EXTERNAL.current_worker": "FAIL",
        "BISIM.machine_step": "GAP",
        "COMPOSE.source_observation": "GAP",
    }
    by_id = {row["id"]: row for row in rows}
    for row_id, expected in required_rows.items():
        actual = by_id.get(row_id, {}).get("status")
        if actual != expected:
            errors.append(f"{row_id}: status={actual!r}, expected={expected}")

    audit_targets = axiom_audit_targets()
    for row_id in sorted(STRICT_AXIOM_AUDIT_ROWS):
        row = by_id.get(row_id)
        if row is None:
            errors.append(f"strict axiom-audit row is absent: {row_id}")
            continue
        if row["status"] != "PASS":
            errors.append(
                f"{row_id}: strict axiom audit requires PASS, got "
                f"{row['status']!r}"
            )
        for reference in row["reference"].split(";"):
            target = reference.strip()
            if not target or target == "-" or "*" in target:
                errors.append(
                    f"{row_id}: non-exact strict audit reference {target!r}"
                )
                continue
            qualified = target if target.startswith("PLeaTTa.") else (
                "PLeaTTa." + target
            )
            if qualified not in audit_targets:
                errors.append(
                    f"{row_id}: reference is not axiom-audited: {target}"
                )
    errors.extend(packet_free_scheduled_consumer_errors())
    return errors


def main() -> int:
    errors = check()
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    _, rows = load_ledger()
    counts = Counter(row["status"] for row in rows)
    summary = " ".join(f"{status}={counts[status]}" for status in sorted(STATUSES))
    print(f"Prolog semantics: {len(rows)} rows; {summary}; trace hash current")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
