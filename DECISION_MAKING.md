# Decision making

This document describes the framework for making decisions in CSLib.

The processes described here are designed to support distributed, consensus-oriented decision making.
They are expected to be followed. However, in general, CSLib is a collaborative project and no procedural framework can anticipate every situation.
When distributed decision making cannot take place because of unavailable area-specific leadership or unresolved disagreement, the Lead Maintainer may intervene as the final decision-making authority (see [exceptional cases](#exceptional-cases)).

## Pull request inclusion

All code merged into CSLib must go through a pull request (PR).

### Review

Every PR must be reviewed before it is merged.

Reviews are not restricted to members of the CSLib reviewer or maintainer teams. We welcome reviews from all contributors and consider reviewing work an important contribution in its own right. Regularly providing thoughtful and constructive reviews is also one of the ways in which contributors can establish the trust that may lead to an invitation to join the CSLib reviewer team.

Members of the CSLib reviewer team are trusted contributors whose technical judgement is recognised by the maintainer team. Maintainers may rely on their reviews as substantive technical scrutiny of the parts of a pull request they have reviewed.

We expect all review comments to be constructive, technically motivated, and aimed at improving the contribution. Whenever possible, comments should be grounded in concrete examples or plausible use cases. When suggesting an alternative, concrete examples are highly welcome.

CSLib strongly encourages reuse of existing infrastructure whenever appropriate, from within CSLib and its dependencies. Reviewers and contributors should therefore consider whether a contribution can build on existing definitions, abstractions, APIs, or results rather than introducing parallel ones. Avoiding unnecessary duplication and fragmentation is an important consideration when evaluating a contribution.

This principle is not absolute. Alternative abstractions or implementations can be valuable when they address limitations of existing infrastructure, support different use cases, or otherwise provide a clear technical benefit. In such cases, contributors should explain the motivation for introducing the alternative and, where relevant, its relationship to existing approaches.

Adding or removing dependencies is managed carefully, taking into account the required CI/CD infrastructure, maintenance implications, and alignment with the broader Lean ecosystem.

Review and acceptance are distinct: a review provides technical scrutiny of a contribution; acceptance authorises its inclusion in CSLib. A maintainer may both review and accept the same PR.

### Acceptance

To be accepted, a PR must:
1. be approved by at least one maintainer; and
2. have all of its substantive parts reviewed.

Reviewers should use their best judgement in determining the scope of their review. A reviewer may consider themselves able to vouch for the PR as a whole, or only for particular parts of it. When the scope is limited, this should be made clear so that additional reviewers can cover the remaining parts. Collectively, the reviews should provide adequate scrutiny of the entire contribution.

When these conditions are satisfied, they are sufficient for merging provided that there are no unresolved objections from members of the CSLib reviewer or maintainer teams.

The decision to merge a pull request must be made by a maintainer. Maintainers act as responsible technical architects of CSLib and are expected to consider the broader coherence and long-term technical direction of the library when accepting contributions.
A maintainer may, at their discretion, delegate the act of merging to a member of the reviewer team. This is commonly done when a pull request has been accepted subject only to minor revisions.

The maintainers authorised to accept pull requests are codified in [CODEOWNERS](/.github/CODEOWNERS).

If a maintainer is the author of a pull request, the required maintainer approval must come from another maintainer. Simple PRs for keeping CSLib up to date with the rest of the Lean ecosystem (e.g., dependency version bumps or fixes to deal with new Lean versions) are exempt from this rule.

### Disagreement

Technical disagreement is a normal and useful part of collaborative development. An objection should therefore be treated as a request to resolve a substantive concern, rather than as a vote against a contribution.

If a member of the CSLib reviewer or maintainer teams raises an objection to a PR, the PR should not be merged while that objection remains unresolved. The participants should first attempt to reach consensus through technical discussion.

Consensus does not require that every participant prefer the final outcome. It means that objections have been considered and resolved sufficiently for the project to move forwards.

When disagreement cannot be resolved through the ordinary review process, the matter may be escalated to the Lead Maintainer. The Lead Maintainer has final authority to resolve such disagreements and determine how the project should proceed.
In doing so, the Lead Maintainer will consider the arguments raised and may seek further feedback from the reviewer and maintainer teams.

## Appointment of reviewers and maintainers

Reviewers and maintainers are trusted members of the CSLib community who are expected to uphold a high standard of collaboration.

New CSLib reviewers and maintainers may be proposed by any member of the CSLib reviewer team, maintainer team, or Steering Committee. Appointment requires affirmative support from at least half of the eligible CSLib voters described below, with no objections after five days of consideration.

Members of the steering committee are not included when calculating the number of votes required for appointment, but may vote for both reviewers and maintainers. Their votes otherwise have the same effect as those of the eligible CSLib voters. The intention is to allow the steering committee members to contribute to appointment decisions without making their participation necessary for reaching the required threshold.

Candidates should be considered on the basis of their contributions to CSLib and the qualities relevant to the role. These may include technical contributions, constructive reviewing activity, subject-matter expertise, reliability, collaboration with other contributors, and commitment to the long-term development of CSLib.

### Reviewers

Candidates for the CSLib reviewer team are discussed and voted on by the current CSLib reviewers and maintainers.

During this process, reviewers and maintainers may privately seek input from other members of the CSLib community or from people who have worked with the candidate.

Members of the Steering Committee are welcome to participate in the discussion of reviewer candidacies.

### Maintainers

Candidates for the CSLib maintainer team are discussed and voted on by the current CSLib maintainers.

During this process, maintainers may privately seek input from reviewers, other members of the CSLib community, or from people who have worked with the candidate.

Members of the Steering Committee are welcome to participate in the discussion of maintainer candidacies.

## Exceptional cases

The ordinary processes described in this document may occasionally be inadequate to resolve a particular situation. Examples include prolonged disagreement, the unavailability of relevant area leadership, or ambiguous responsibility.

In such cases, the Lead Maintainer may intervene to determine how a decision should be made to move the project forwards.

## Maintenance of these policies

The [CODEOWNERS](/.github/CODEOWNERS) file is maintained by the lead maintainer, who is also responsible for coordinating changes to this document and related CSLib governance policies.
