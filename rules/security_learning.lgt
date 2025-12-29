%% SPDX-License-Identifier: MIT OR Palimpsest-0.6
%% ECHIDNA Security Rule Learning Module
%% Learns security patterns from cicd-hyper-a audit data

:- object(security_learning).

    :- info([
        version is 1:'0':'0',
        author is 'ECHIDNA Project Team',
        date is 2025-12-29,
        comment is 'Neurosymbolic learning module for security rule extraction'
    ]).

    %% Public predicates
    :- public([
        load_training_data/1,       % Load from cicd-hyper-a
        learn_rules/0,              % Learn rules from loaded data
        export_rules/1,             % Export learned rules
        suggest_fix/2,              % Suggest fix for alert type
        classify_severity/2,        % Classify alert severity
        is_auto_fixable/1,          % Check if auto-fixable
        get_prevention_workflow/2   % Get prevention workflow for alert type
    ]).

    :- private([
        training_data/3,            % Stored training examples
        learned_rule/4,             % Learned rules
        fix_pattern/3               % Fix patterns
    ]).

    :- dynamic([
        training_data/3,
        learned_rule/4,
        fix_pattern/3
    ]).

    %% ============================================================
    %% Core Alert Categories (from ERROR-CATALOG.scm)
    %% ============================================================

    alert_category('TokenPermissionsID', workflow_security).
    alert_category('PinnedDependenciesID', workflow_security).
    alert_category('missing-workflow-permissions', workflow_security).

    alert_category('hard-coded-cryptographic-value', code_security).
    alert_category('remote-property-injection', code_security).
    alert_category('sql-injection', code_security).

    alert_category('unused-local-variable', code_quality).
    alert_category('syntax-error', code_quality).

    alert_category('VulnerabilitiesID', dependency_vuln).
    alert_category('unmaintained', dependency_vuln).

    alert_category('SecurityPolicyID', process_hygiene).
    alert_category('MaintainedID', process_hygiene).
    alert_category('CodeReviewID', process_hygiene).
    alert_category('BranchProtectionID', process_hygiene).
    alert_category('CIIBestPracticesID', process_hygiene).

    alert_category('FuzzingID', missing_tests).
    alert_category('SASTID', missing_tests).
    alert_category('CITestsID', missing_tests).

    %% ============================================================
    %% Severity Classification
    %% ============================================================

    classify_severity(AlertType, critical) :-
        member(AlertType, [
            'hard-coded-cryptographic-value',
            'sql-injection',
            'VulnerabilitiesID'
        ]), !.

    classify_severity(AlertType, high) :-
        member(AlertType, [
            'remote-property-injection',
            'TokenPermissionsID',
            'missing-workflow-permissions'
        ]), !.

    classify_severity(AlertType, medium) :-
        member(AlertType, [
            'PinnedDependenciesID',
            'SecurityPolicyID',
            'BranchProtectionID',
            'CodeReviewID',
            'syntax-error'
        ]), !.

    classify_severity(_, low).

    %% ============================================================
    %% Auto-Fixable Detection
    %% ============================================================

    is_auto_fixable('TokenPermissionsID').
    is_auto_fixable('PinnedDependenciesID').
    is_auto_fixable('missing-workflow-permissions').
    is_auto_fixable('SecurityPolicyID').
    is_auto_fixable('BranchProtectionID').
    is_auto_fixable('unused-local-variable').

    %% ============================================================
    %% Fix Suggestions
    %% ============================================================

    suggest_fix('TokenPermissionsID', 'Add "permissions: read-all" at workflow level').
    suggest_fix('PinnedDependenciesID', 'Replace @v4 with @SHA # v4 format').
    suggest_fix('missing-workflow-permissions', 'Add "permissions: read-all" at workflow level').
    suggest_fix('SecurityPolicyID', 'Create SECURITY.md with vulnerability reporting instructions').
    suggest_fix('BranchProtectionID', 'Enable branch protection via Settings > Branches').
    suggest_fix('CodeReviewID', 'Require at least 1 approving review before merge').
    suggest_fix('CIIBestPracticesID', 'Register at bestpractices.coreinfrastructure.org').
    suggest_fix('FuzzingID', 'Add ClusterFuzzLite or cargo-fuzz infrastructure').
    suggest_fix('VulnerabilitiesID', 'Run cargo audit / npm audit and update dependencies').
    suggest_fix('hard-coded-cryptographic-value', 'Use environment variables or secrets manager').
    suggest_fix('remote-property-injection', 'Add allowlist validation for dynamic property access').
    suggest_fix('unused-local-variable', 'Remove unused code or prefix with underscore').
    suggest_fix('syntax-error', 'Fix syntax error using linter output').

    %% ============================================================
    %% Prevention Workflows
    %% ============================================================

    get_prevention_workflow('TokenPermissionsID', 'workflow-linter.yml').
    get_prevention_workflow('PinnedDependenciesID', 'workflow-linter.yml').
    get_prevention_workflow('missing-workflow-permissions', 'workflow-linter.yml').
    get_prevention_workflow('hard-coded-cryptographic-value', 'secret-scanner.yml').
    get_prevention_workflow('VulnerabilitiesID', 'cargo-audit.yml').
    get_prevention_workflow('SecurityPolicyID', 'scorecard-enforcer.yml').
    get_prevention_workflow('BranchProtectionID', 'branch-protection-enforcer.yml').

    %% ============================================================
    %% Learning from Training Data
    %% ============================================================

    %% Load training data from cicd-hyper-a ERROR-CATALOG.scm
    load_training_data(FilePath) :-
        open(FilePath, read, Stream),
        read_training_examples(Stream),
        close(Stream).

    read_training_examples(Stream) :-
        read(Stream, Term),
        ( Term == end_of_file ->
            true
        ; process_training_term(Term),
          read_training_examples(Stream)
        ).

    process_training_term(error(Id, Type, Severity, AutoFix, Description, Fix)) :-
        assertz(training_data(Id, Type, fix(Description, Fix, AutoFix))),
        assertz(learned_rule(Id, Type, Severity, AutoFix)).

    process_training_term(_). % Ignore unknown terms

    %% Learn rules by analyzing training data patterns
    learn_rules :-
        findall(
            rule(AlertType, Category, Severity, AutoFix),
            (
                training_data(AlertType, Category, _),
                classify_severity(AlertType, Severity),
                (is_auto_fixable(AlertType) -> AutoFix = true ; AutoFix = false)
            ),
            Rules
        ),
        forall(
            member(rule(A, C, S, F), Rules),
            assertz(learned_rule(A, C, S, F))
        ).

    %% Export learned rules to file
    export_rules(FilePath) :-
        open(FilePath, write, Stream),
        write(Stream, '%% Learned security rules\n'),
        write(Stream, '%% Generated by ECHIDNA security_learning module\n\n'),
        forall(
            learned_rule(AlertType, Category, Severity, AutoFix),
            (
                format(Stream, 'security_rule(~q, ~q, ~q, ~q).~n',
                       [AlertType, Category, Severity, AutoFix])
            )
        ),
        close(Stream).

:- end_object.


%% ============================================================
%% Integration with cicd-hyper-a
%% ============================================================

:- object(cicd_integration).

    :- info([
        version is 1:'0':'0',
        comment is 'Integration layer between cicd-hyper-a and ECHIDNA'
    ]).

    :- public([
        sync_from_cicd/0,           % Sync training data from cicd-hyper-a
        push_rules_to_cicd/0,       % Push learned rules back
        validate_alert/2            % Validate an alert against learned rules
    ]).

    %% Path to cicd-hyper-a repository
    cicd_repo_path('~/repos/cicd-hyper-a/.audittraining').

    %% Sync training data from cicd-hyper-a
    sync_from_cicd :-
        cicd_repo_path(BasePath),
        atom_concat(BasePath, '/ERROR-CATALOG.scm', CatalogPath),
        security_learning::load_training_data(CatalogPath),
        security_learning::learn_rules.

    %% Push learned rules back to cicd-hyper-a
    push_rules_to_cicd :-
        cicd_repo_path(BasePath),
        atom_concat(BasePath, '/echidna-rules.lgt', RulesPath),
        security_learning::export_rules(RulesPath).

    %% Validate an alert
    validate_alert(AlertType, Result) :-
        security_learning::classify_severity(AlertType, Severity),
        security_learning::suggest_fix(AlertType, Fix),
        (security_learning::is_auto_fixable(AlertType) ->
            AutoFix = true ; AutoFix = false),
        Result = alert_validation(AlertType, Severity, Fix, AutoFix).

:- end_object.
