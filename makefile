all: IamNotProvable.vo

EnumSeqNat.vo: EnumSeqNat.v
	coqc EnumSeqNat.v

ChineseRemainder.vo: ChineseRemainder.v EnumSeqNat.vo
	coqc ChineseRemainder.v

Formulas.vo: Formulas.v EnumSeqNat.vo
	coqc Formulas.v

Substitutions.vo: Substitutions.v Formulas.vo
	coqc Substitutions.v

IsFreeForSubst.vo: IsFreeForSubst.v Substitutions.vo
	coqc IsFreeForSubst.v

Proofs.vo: Proofs.v IsFreeForSubst.vo
	coqc Proofs.v

ProofTactics.vo: ProofTactics.v Proofs.vo
	coqc ProofTactics.v

PeanoAxioms.vo: PeanoAxioms.v ProofTactics.vo
	coqc PeanoAxioms.v

HeytingModel.vo: HeytingModel.v PeanoAxioms.vo Proofs.vo
	coqc HeytingModel.v

PeanoModel.vo: PeanoModel.v HeytingModel.vo Proofs.vo
	coqc PeanoModel.v

HeytingRepresentation.vo: HeytingRepresentation.v HeytingModel.vo ProofTactics.vo
	coqc HeytingRepresentation.v

BoolRepresented.vo: BoolRepresented.v HeytingRepresentation.vo BetaRepr.vo
	coqc BoolRepresented.v

BetaRepr.vo: BetaRepr.v HeytingRepresentation.vo ProofTactics.vo ChineseRemainder.vo
	coqc BetaRepr.v

EnumSeqNat_repr.vo: EnumSeqNat_repr.v BetaRepr.vo BoolRepresented.vo
	coqc EnumSeqNat_repr.v

IsProof_repr.vo: IsProof_repr.v EnumSeqNat_repr.vo BoolRepresented.vo
	coqc IsProof_repr.v

DeductionTheorem.vo: DeductionTheorem.v ProofTactics.vo
	coqc DeductionTheorem.v

Consistency.vo: Consistency.v IsProof_repr.vo HeytingModel.vo
	coqc Consistency.v

IamNotProvable.vo: IamNotProvable.v Consistency.vo PeanoModel.vo DeductionTheorem.vo
	coqc IamNotProvable.v

clean:
	rm --force *~ *.vo *.vok .*.aux *.glob *.vos
