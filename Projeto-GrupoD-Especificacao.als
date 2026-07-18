sig Partida {
	jogo: one Jogo,
	mesa: one Mesa,
	horario: one Horario,
	participantes: set Jogador,
	organizador: one Jogador
}

sig Jogo {
	categoria: one Categoria
}

abstract sig Categoria {}
one sig Estrategia extends Categoria {}
one sig Party extends Categoria {}
one sig Cooperativo extends Categoria {}

sig Jogador {}

sig Mesa {}

sig Horario {}

fact SemConflitoDeHorarioParaJogador {
  all j: Jogador |
    all disj p1, p2: Partida |
      (j in p1.participantes + p1.organizador and
       j in p2.participantes + p2.organizador)
      implies p1.horario != p2.horario
}

fact SemConflitoDeMesa {
  all disj p1, p2: Partida |
    (p1.mesa = p2.mesa) implies (p1.horario != p2.horario)
}

fact QuantidadeDeParticipantes {
  all p: Partida |
    #p.participantes >= 2 and #p.participantes <= 6
}

fact OrganizadorEhParticipante {
  all p: Partida |
    p.organizador in p.participantes
}

