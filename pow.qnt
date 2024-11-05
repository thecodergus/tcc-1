module pow {
    // Define o tipo Node como uma string (identificador de nó)
    type Node = str

    // Definindo uma variante para miner_id que pode ser "First" ou um Node
    type MinerId =
        | First       // Representa o bloco inicial, valor especial
        | Miner(Node) // Representa o minerador por um Node

    // Enumeradores para o estado do minerador
    type MinerStatus =
        | MINED
        | MINER

    // Tipo Block, onde miner_id agora usa a variante MinerId
    type Block = {
        miner_id: MinerId,       // "First" ou um Node encapsulado em Miner
        block_id: int,           // Deve estar no intervalo 0..3
        prev_block_id: int       // Deve estar no intervalo -1..3
    }

    // Variáveis de estado que representam os blocos e as propriedades na cadeia
    const nodes: Set[Node]                    // Conjunto de nós mineradores
    var blcks: Set[Block]                     // Conjunto de blocos válidos
    var chain: Node -> Set[Block]             // Cada nó aponta para um subconjunto de blocos
    var last_block_id: Node -> int            // Último bloco minerado por cada nó (0 a 3)
    var status: Node -> MinerStatus           // Estado do nó, valores MINED ou MINER
    var status_changer: Node -> int           // Indicador de mudança de status, valores 0 ou 1

    // Função para verificar se um bloco é válido conforme as restrições definidas
    def isValidBlock(b: Block): bool = and {
        b.block_id >= 0 and b.block_id <= 3,
        b.prev_block_id >= -1 and b.prev_block_id <= 3
    }

    // Ação para verificar todas as condições de tipo
    action POWTypeOK: bool = all {
        // Verifica se todos os elementos de blcks seguem o tipo Block
        blcks.forall(isValidBlock),

        // Verifica se chain é um mapeamento de nodes para subconjuntos de Block
        nodes.forall(n => chain.get(n).subseteq(blcks)),

        // Verifica se last_block_id é um mapeamento de nodes para valores entre 0 e 3
        nodes.forall(n => last_block_id.get(n) >= 0 and last_block_id.get(n) <= 3),

        // Verifica se status é um mapeamento de nodes para MINED ou MINER
        nodes.forall(n => Set(MINED, MINER).contains(status.get(n))),

        // Verifica se status_changer é um mapeamento de nodes para 0 ou 1
        nodes.forall(n => Set(0, 1).contains(status_changer.get(n)))
    }

     action POWInitOK: bool = all {
        // Inicializa blcks com o bloco inicial
        blcks == Set({
            miner_id: First,
            block_id: 0,
            prev_block_id: -1
        }),

        // Inicializa chain, mapeando cada nó para um conjunto contendo o bloco inicial
        chain == nodes.mapBy(n => Set({
            miner_id: First,
            block_id: 0,
            prev_block_id: -1
        })),

        // Inicializa last_block_id, mapeando cada nó para 0
        last_block_id == nodes.mapBy(n => 0),

        // Inicializa status, mapeando cada nó para MINER
        status == nodes.mapBy(n => MINER),

        // Inicializa status_changer, mapeando cada nó para 0
        status_changer == nodes.mapBy(n => 0)
    }


    // Função de mineração de um bloco por um nó
    action MineABlock(n: Node): bool = all {
        // Verifica se o status do nó é MINER
        status.get(n) == MINER,

        // Atualiza chain para incluir o novo bloco para o nó n
        chain' = chain.set(n, chain.get(n).union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n) + 1,
            prev_block_id: last_block_id.get(n)
        }))),

        // Adiciona o novo bloco ao conjunto blcks
        blcks' = blcks.union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n) + 1,
            prev_block_id: last_block_id.get(n)
        })),

        // Incrementa last_block_id para o nó n
        last_block_id' = last_block_id.set(n, last_block_id.get(n) + 1),

        // Atualiza o status do nó n para MINED
        status' = status.set(n, MINED),

        // Define status_changer para 1 para o nó n
        status_changer' = status_changer.set(n, 1)
    }

    // Ação para confirmar um bloco minerado por um nó
    action CommitABlock(n: Node, r: Node): bool = all {
        // Verifica se o status de n é MINED
        status.get(n) == MINED,

        // Verifica se o last_block_id de r é o ID anterior ao de n
        last_block_id.get(r) == last_block_id.get(n) - 1,

        // Verifica se o bloco minerado por n está presente em blcks
        blcks.contains({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(n) - 1
        }),

        // Atualiza chain para o nó r, incluindo o novo bloco
        chain' = chain.set(r, chain.get(r).union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(r)
        }))),

        // Atualiza last_block_id para que o ID de r seja igual ao de n
        last_block_id' = last_block_id.set(r, last_block_id.get(n)),

        // Define status_changer para 1 para o nó r
        status_changer' = status_changer.set(r, 1),

        // Garante que blcks e status permanecem inalterados
        blcks' = blcks,
        status' = status
    }

    // Ação para ignorar um bloco minerado por um nó
    action IgnoreABlock(n: Node, r: Node): bool = all {
        // Verifica se o status de n é MINED
        status.get(n) == MINED,

        // Verifica se o bloco minerado por n com os IDs correspondentes está presente em blcks
        blcks.contains({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(n) - 1
        }),

        // Define status_changer para 1 para o nó r
        status_changer' = status_changer.set(r, 1),

        // Garante que chain, blcks, last_block_id e status permanecem inalterados
        chain' = chain,
        blcks' = blcks,
        last_block_id' = last_block_id,
        status' = status
    }

    // Ação para mudar o status de um nó
    action ChangeStatus(n: Node): bool = all {
        // Define status_changer para 1 para todos os nós inicialmente
        status_changer == nodes.mapBy(_ => 1),

        // Atualiza o status do nó n para MINER
        status' = status.set(n, MINER),

        // Define status_changer para 0 para todos os nós no próximo estado
        status_changer' = nodes.mapBy(_ => 0),

        // Garante que blcks, chain e last_block_id permanecem inalterados
        blcks' = blcks,
        chain' = chain,
        last_block_id' = last_block_id
    }

    // Ação de transição principal, que executa uma das alternativas para um nó escolhido
    action POWNext = any {
        // Escolhe um nó `n` de forma não-determinística
        nondet n = oneOf(nodes)

        // Executa uma das ações alternativas para `n`
        any {
            // Alternativa 1: MineABlock para `n`
            MineABlock(n),

            // Alternativa 2: ChangeStatus para `n`
            ChangeStatus(n),

            // Alternativa 3: Para todos os nós `r`, executa CommitABlock ou IgnoreABlock
            all {
                nondet r = oneOf(nodes)
                any {
                    CommitABlock(n, r),
                    IgnoreABlock(n, r)
                }
            }
        }
    }

    // Definimos os vars para usar com orKeep
    val vars = (chain, blcks, last_block_id, status)

    // Especificação do protocolo de prova de trabalho usando orKeep
    temporal POWSpec = POWInitOK implies always(POWNext.orKeep(vars))

}
