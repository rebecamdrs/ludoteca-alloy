module Cenarios_Experimentais
open Projeto_GrupoD_Especificacao

assert TestPartidasOrganizadas{
	all j : Jogador |
		all p : Partida |
			(p in partidasOrganizadas[j]) iff (p.organizador = j)
}


pred CenarioPartidasOrganizadas {
	some j: Jogador |
		some p: Partida |
			p.organizador = j and
			p in partidasOrganizadas[j]
}


assert TestPartidasComoParticipante{
	all j: Jogador |
		all p: Partida |
			(p in partidasComoParticipante[j]) iff ( j in p.participantes and p.organizador != j)
}
check  TestPartidasComoParticipante for 5

pred CenarioPartidasComoParticipante{
	some j: Jogador |
		some p: Partida |
			j in p.participantes and p.organizador != j and p in partidasComoParticipante[j]
}
run  CenarioPartidasComoParticipante  for 5

